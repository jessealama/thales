import Thales.TypeCheck.TSAST
import Thales.TypeCheck.Context
import Thales.TypeCheck.Generic
import Thales.Emit.LeanSyntax
import Thales.Emit.EscapeAnalysis
import Std.Data.HashMap

namespace Thales.Emit

open Thales.AST
open Thales.TypeCheck
open Thales.Emit.LeanSyntax

/-- Type environment threaded through `emitBodyEnv`. `throwTypes` is non-empty
    iff the enclosing function has a `@throws ...` annotation; when non-empty,
    returns become `.ok` and `throw` becomes `Except.error <inj>`. -/
structure EmitEnv where
  aliasEnv      : Std.HashMap String TSType := {}
  bindingEnv    : Std.HashMap String TSType := {}
  retTy         : Option TSType := none
  throwTypes    : List String := []
  funcThrowsEnv : Std.HashMap String (List String) := {}
  -- Map from function name → parameter types (in order). Used at call
  -- sites to coerce numeric literal arguments into refinement-typed slots.
  funcParamTypes : Std.HashMap String (List TSType) := {}
  -- Map from function name → declared return type (normalized). Lets an
  -- un-annotated `const x = f(...)` record x's binding so Option-narrowing
  -- can fire on it.
  funcRetTypes : Std.HashMap String TSType := {}
  -- Map from interface / single-record-alias name → declared fields in
  -- declared order. Lets object-literal construction resolve the target
  -- structure and field types (#15/#81).
  structFields : Std.HashMap String (List (String × TSType)) := {}
  -- Counter used to generate unique dite-binder names. Bumped each time
  -- a fresh `h_i` is introduced (e.g. for `is<T>`-narrowing shadow-lets).
  diteBinderCounter : Nat := 0
  -- Inside a class method body, the Lean receiver name `this` lowers to
  -- (`self'`); `none` outside class scopes (#106).
  thisName : Option String := none
  -- Inside a v1 constructor body, `this.<f>` reads lower to the field-local
  -- `let f` binding instead of a projection (#106).
  ctorMode : Bool := false
  -- Map from local class name → ctor param types (declared order). Drives
  -- `new C(args)` → `C.ctor' args` with expected-type direction (#106).
  classCtorParams : Std.HashMap String (List (String × TSType)) := {}
  -- Value names bound by import specifiers. `new C(args)` on an imported
  -- name lowers to `C.ctor' args` without expected-type direction (#106).
  importedNames : Std.HashSet String := {}

/-- Binary ops lowered through JS-semantics runtime helpers (#32) instead
    of bare Lean operators: no Float instances exist for these, and the JS
    semantics (ToInt32 wrap, dividend-sign `%`) differ anyway. -/
private def jsBinopHelper : BinaryOperator → Option String
  | .mod    => some "jsMod"
  | .bitand => some "jsBitAnd"
  | .bitor  => some "jsBitOr"
  | .bitxor => some "jsBitXor"
  | .shl    => some "jsShl"
  | .shr    => some "jsShr"
  | .ushr   => some "jsUShr"
  | _ => none

/-- Resolve a TSType through one level of type-alias references. -/
private def resolveTypeAlias (env : EmitEnv) : TSType → TSType
  | .ref name _ =>
    match env.aliasEnv.get? name with
    | some resolved => resolved
    | none => .ref name []
  | .paren inner => resolveTypeAlias env inner
  | other => other

/-- The element type of `name`, when its binding resolves to an array type;
    `none` otherwise. Loop lowering (#25) keys on this: SubsetCheck only
    admits array operands, so a `none` here means the phases drifted and the
    caller must emit the loud marker rather than miscompile. -/
private def arrayElemTy? (env : EmitEnv) (name : String) : Option TSType :=
  match env.bindingEnv.get? name with
  | some rawTy =>
      match resolveTypeAlias env rawTy with
      | .array et => some et
      | _ => none
  | none => none

/-- If every branch of a union shares one underlying primitive (all string
    literals, or all numeric literals, or all boolean literals), return that
    primitive. Used to lower `1 | 2 | 3` to `Float`, `"a" | "b"` to `String`,
    etc. — the constraint is lost on the Lean side, but the resulting type
    is what value-level returns can elaborate against. -/
private def commonLiteralPrimitive (branches : List TSType) : Option LType :=
  let rec stripParen : TSType → TSType
    | .paren t => stripParen t
    | t => t
  -- Use a tag string to compare branch primitives without needing BEq LType.
  let tag : TSType → Option String := fun t => match stripParen t with
    | .stringLit _ => some "String"
    | .numberLit _ => some "Float"
    | .booleanLit _ => some "Bool"
    | _ => none
  match branches with
  | [] => none
  | first :: _ =>
    match tag first with
    | none => none
    | some k =>
      if branches.all (fun b => tag b == some k) then some (.const k) else none

/-- Translate a TS type to a Lean type. -/
partial def emitType : TSType → LType
  | .number => .const "Float"
  | .bigint => .const "Int"
  | .string => .const "String"
  | .boolean => .const "Bool"
  | .stringLit _ => .const "String"
  | .numberLit _ => .const "Float"
  | .booleanLit _ => .const "Bool"
  -- Refinement subtypes of number map to their Lean Subtype abbreviations.
  | .refinement k => .const k.name
  | .array elem => .app "Array" [emitType elem]
  | .tuple elems =>
    match elems with
    | [] => .const "Unit"
    | [t] => emitType t
    | t :: rest => rest.foldl (fun acc ty => .prod acc (emitType ty)) (emitType t)
  | .option inner => .app "Option" [emitType inner]
  -- Nullable union: T | null or T | undefined → Option T.
  -- Same-primitive literal union: lower to that primitive.
  | .union types =>
    match normalizeNullableUnion types with
    | some (.option inner) => .app "Option" [emitType inner]
    | _ =>
      match commonLiteralPrimitive types with
      | some prim => prim
      | none => .const "Unit"  -- non-nullable, mixed-shape union: placeholder
  | .ref name args => if args.isEmpty then .const name else .app name (args.map emitType)
  | .typeVar _ name _ => .var name
  | .function ps ret =>
      let paramTys := ps.map fun (.mk _ t _ _) => emitType t
      paramTys.foldr (fun p acc => .arrow p acc) (emitType ret)
  | .paren inner => emitType inner
  | .object _ => .const "Unit"  -- anonymous object types not emitted; v1 uses named structures only
  | _ => .const "Unit"

/-- Try to extract a discriminated shape from a union's branch list.
    Returns `some (ctorName, fields)` for each branch when the union is
    discriminated (every branch is a `.object` that shares at least one
    string-literal property name).  Returns `none` otherwise. -/
private def asDiscriminated
    (branches : List TSType) : Option (List (String × List (String × TSType))) := Id.run do
  if branches.length < 2 then return none
  -- Collect string-literal property names for a single branch
  let stringLitProps : TSType → List String := fun b =>
    match b with
    | .object ms => ms.filterMap fun
        | .property n (.stringLit _) _ _ => some n
        | _ => none
    | _ => []
  -- Find a property name that is a string-literal discriminator in every branch
  let firstProps := stringLitProps branches.head!
  let discCandidates := firstProps.filter fun name =>
    branches.all fun b => (stringLitProps b).contains name
  let discName ← discCandidates.head?
  -- For each branch produce (ctorValue, remaining fields)
  let results : List (Option (String × List (String × TSType))) := branches.map fun b =>
    match b with
    | .object ms =>
        let discVal : Option String := ms.findSome? fun
          | .property n (.stringLit v) _ _ => if n == discName then some v else none
          | _ => none
        discVal.map fun v =>
          let fields : List (String × TSType) := ms.filterMap fun
            | .property n ty _ _ => if n == discName then none else some (n, ty)
            | _ => none
          (v, fields)
    | _ => none
  -- All branches must have resolved to `some`
  if results.any Option.isNone then return none
  return some (results.filterMap id)

/-- Encode an arbitrary string for use inside a Lean `«…»` constructor
    name. `»` closes the escape, so it can't appear; backslashes and
    quotes inside the source string also need escaping so the rendered
    constructor name parses cleanly. Returns `none` when the input
    contains a `»` we cannot encode. -/
private def escapeLitCtorName (s : String) : Option String := Id.run do
  let mut out : String := ""
  for c in s.toList do
    match c with
    | '»' => return none
    | '\n' => out := out ++ "\\n"
    | '\r' => out := out ++ "\\r"
    | '\t' => out := out ++ "\\t"
    | '\\' => out := out ++ "\\\\"
    | '\"' => out := out ++ "\\\""
    | _ => out := out.push c
  return some out

/-- Render a literal TS type as the textual form used inside a Lean
    `«…»` constructor name. Returns `none` when the literal contains
    a character we cannot encode. -/
private def literalCtorText : TSType → Option String
  | .stringLit s => (escapeLitCtorName s).map fun safe => s!"\"{safe}\""
  | .numberLit n =>
      let str := toString n
      -- toString renders an integer-valued Float as e.g. "1.000000".
      -- Drop trailing zeros so the constructor name matches user intuition;
      -- if the result ends with `.`, drop that too (yields `«1»` for `1`,
      -- `«-1»` for `-1`, but keeps `«3.14»` for `3.14`).
      let trimmed :=
        if str.contains '.' then
          let revChars := str.toList.reverse.dropWhile (· == '0')
          let revChars := if revChars.head? = some '.' then revChars.tail else revChars
          String.ofList revChars.reverse
        else str
      some trimmed
  | .booleanLit true  => some "true"
  | .booleanLit false => some "false"
  | .paren inner      => literalCtorText inner
  | _ => none

/-- Build the `«…»` constructor name (no leading dot) for one branch. -/
private def literalCtorName (ty : TSType) : Option String :=
  literalCtorText ty |>.map fun text => s!"«{text}»"

/-- Build the LExpr value that the Coe instance maps a constructor to —
    the underlying-primitive form of the literal. -/
private def literalCtorValueExpr : TSType → Option LExpr
  | .stringLit s     => some (.str s)
  | .numberLit n     => some (.float n)
  | .booleanLit b    => some (.bool b)
  | .paren inner     => literalCtorValueExpr inner
  | _ => none

/-- The `(name, type)` property fields of an object type, in declared order,
    dropping methods and index signatures. Single source for structure-field
    emission (#13) and the `structFields` construction env (#15/#81). -/
private def objectTypeFields (members : List TSObjectMember) : List (String × TSType) :=
  members.filterMap fun
    | .property f t _ _ => some (f, t)
    | _ => none

/-- The `(name, type)` property fields of an interface, in declared order,
    dropping methods. -/
private def interfaceFields (members : List TSInterfaceMember) : List (String × TSType) :=
  members.filterMap fun
    | .property f t _ _ => some (f, t)
    | _ => none

/-- The `(key, valueExpr)` entries of an object literal, covering shorthand
    (`{ x }`) and explicit (`{ x: e }`) properties; spreads and computed keys
    are dropped. Shared by the discriminated-union ctor path and struct
    construction (#15/#81). -/
private def objectLiteralEntries (props : List ObjectProperty) : List (String × Expression) :=
  props.filterMap fun
    | .regular _ (.literal _ (.string k) _) v _ _ _ => some (k, v)
    | .regular _ (.identifier _ k) v _ _ _          => some (k, v)
    | _                                             => none

/-- Emit a type alias.
    - Discriminated object unions become Lean `inductive` types.
    - Same-primitive literal unions (`-1 | 0 | 1`, `"a" | "b"`, `true | false`)
      become an `inductive` plus a companion `Coe Foo Prim` instance so the
      value still flows into arithmetic/string contexts via Lean's automatic
      coercion insertion.
    - Everything else falls back to an `abbrev`.

    Returns a list because the literal-union case produces two decls. -/

def emitTypeAlias (name : String) (typeParams : List String) (ty : TSType) : List LDecl :=
  match ty with
  | .union branches =>
      match asDiscriminated branches with
      | some ctors =>
          let leanCtors := ctors.map fun (ctorName, fields) =>
            (ctorName, fields.map fun (fn, fty) => (fn, emitType fty))
          [.inductive_ name typeParams leanCtors]
      | none =>
          match commonLiteralPrimitive branches,
                branches.mapM literalCtorName,
                branches.mapM literalCtorValueExpr with
          | some prim, some ctorNames, some ctorVals =>
              let leanCtors : List (String × List (String × LType)) :=
                ctorNames.map fun n => (n, [])
              let arms : List (LPattern × LExpr) :=
                ctorNames.zip ctorVals |>.map fun (n, v) => (.ctor n [], v)
              let coeBody : LExpr :=
                .lam [("v__", none)] (.match_ (.var "v__") arms)
              [.inductive_ name typeParams leanCtors,
               .instance_ (.app "Coe" [.const name, prim]) "coe" coeBody]
          | _, _, _ => [.abbrev_ name typeParams (emitType ty)]
  | .object members =>
      let fields := (objectTypeFields members).map fun (n, t) => (n, emitType t)
      [.struct name typeParams fields]
  | _ => [.abbrev_ name typeParams (emitType ty)]

/-- Emit an interface as a Lean structure. Only property members are
    kept for v1; method members are skipped (v2 adds classes/methods). -/
def emitInterface (name : String) (typeParams : List String)
    (members : List TSInterfaceMember) : LDecl :=
  let fields := (interfaceFields members).map fun (n, t) => (n, emitType t)
  .struct name typeParams fields

/-- Extract type-param names from a list of TSTypeParam. -/
private def typeParamNames (tps : List TSTypeParam) : List String :=
  tps.map (·.name)

/-- Build a Lean list literal from a list of expressions.
    `[]` becomes `.var "List.nil"`;
    `[x, y]` becomes `.app (.var "List.cons") [x, .app (.var "List.cons") [y, .var "List.nil"]]`. -/
private def mkListLit (elems : List LExpr) : LExpr :=
  elems.foldr (fun x acc => .app (.var "List.cons") [x, acc]) (.var "List.nil")

/-- Map a JS binary operator to its Lean string representation. -/
private def binaryOpStr : BinaryOperator → String
  | .eq  => "=="   -- JS == (loose); map to Lean == for now
  | .neq => "!="
  | .seq => "=="   -- JS === maps to Lean ==
  | .sneq => "!="  -- JS !== maps to Lean !=
  | .lt  => "<"
  | .leq => "<="
  | .gt  => ">"
  | .geq => ">="
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "%"
  | .exp => "^"
  | .bitor   => "|||"
  | .bitxor  => "^^^"
  | .bitand  => "&&&"
  | .shl     => "<<<"
  | .shr     => ">>>"
  | .ushr    => ">>>"   -- no unsigned shift in Lean; use signed as placeholder
  | .«in»    => "∈"     -- placeholder
  | .instanceof => "instanceof"  -- placeholder

/-- Rewrite every `scrutName.fieldName` sub-expression to `.var fieldName`.
    Used to substitute destructured fields in a switch arm body before emission. -/
private partial def substMemberAccessExpr (scrutName : String) : Expression → Expression
  | .memberExpr b (.identifier ib n) prop false opt =>
    if n == scrutName then
      -- Rewrite `scrutName.field` → bare `field` identifier
      match prop with
      | .identifier ip f => .identifier ip f
      | other => .memberExpr b (.identifier ib n) other false opt
    else
      .memberExpr b (.identifier ib n) (substMemberAccessExpr scrutName prop) false opt
  | .memberExpr b obj prop comp opt =>
      .memberExpr b (substMemberAccessExpr scrutName obj)
                    (substMemberAccessExpr scrutName prop) comp opt
  | .binaryExpr b op l r =>
      .binaryExpr b op (substMemberAccessExpr scrutName l) (substMemberAccessExpr scrutName r)
  | .logicalExpr b op l r =>
      .logicalExpr b op (substMemberAccessExpr scrutName l) (substMemberAccessExpr scrutName r)
  | .unaryExpr b op pref arg =>
      .unaryExpr b op pref (substMemberAccessExpr scrutName arg)
  | .conditionalExpr b c t e =>
      .conditionalExpr b (substMemberAccessExpr scrutName c)
                         (substMemberAccessExpr scrutName t)
                         (substMemberAccessExpr scrutName e)
  | .callExpr b callee args opt =>
      .callExpr b (substMemberAccessExpr scrutName callee)
                  (args.map (substMemberAccessExpr scrutName)) opt
  | .arrayExpr b elems =>
      .arrayExpr b (elems.map (Option.map (substMemberAccessExpr scrutName)))
  -- #24: switch arms may contain mutation; substitute inside the RHS
  -- (the target identifier is a local, never `scrutName.field`).
  | .assignmentExpr b op target rhs =>
      .assignmentExpr b op target (substMemberAccessExpr scrutName rhs)
  | other => other

/-- Rewrite `scrutName.field` in all expressions within a statement. -/
private partial def substMemberAccessStmt (scrutName : String) : Statement → Statement
  | .returnStmt b (some e)  => .returnStmt b (some (substMemberAccessExpr scrutName e))
  | .returnStmt b none      => .returnStmt b none
  | .exprStmt b e           => .exprStmt b (substMemberAccessExpr scrutName e)
  | .blockStmt b stmts      => .blockStmt b (stmts.map (substMemberAccessStmt scrutName))
  | .ifStmt b cond thn els  =>
      .ifStmt b (substMemberAccessExpr scrutName cond)
               (substMemberAccessStmt scrutName thn)
               (els.map (substMemberAccessStmt scrutName))
  | .variableDecl (.mk b decls k) =>
      .variableDecl (.mk b (decls.map fun
        | .mk db pat (some init) ann =>
            .mk db pat (some (substMemberAccessExpr scrutName init)) ann
        | d => d) k)
  | other => other

/-- Extract the null/undefined-checked variable from an equality test
    against `null` or `undefined` (either operand order). Returns the
    variable name and the test's polarity: `true` for `===`/`==` (the THEN
    branch is the nullish side), `false` for `!==`/`!=` (#43 — the THEN
    branch is the narrowed, non-nullish side). Returns `none` for other
    conditions. -/
private def nullCheckVar : Expression → Option (String × Bool)
  | .binaryExpr _ op l r =>
    let polarity : Option Bool := match op with
      | .seq | .eq => some true
      | .sneq | .neq => some false
      | _ => none
    let isNullish : Expression → Bool
      | .literal _ .null _ => true
      | .identifier _ "undefined" => true
      | _ => false
    let subjectOf : Expression → Expression → Option String := fun a b =>
      match a with
      | .identifier _ n => if isNullish b && n != "undefined" then some n else none
      | _ => none
    match polarity with
    | some pos => (subjectOf l r <|> subjectOf r l).map (·, pos)
    | none => none
  | _ => none

/-- If `targetTy` resolves through `aliasEnv` to a same-primitive literal
    union and `expr` is a literal whose value matches one of the union's
    branches, return the LExpr that elaborates against the inductive
    (i.e. `.matched-ctor`). Returns `none` to mean "fall through to the
    normal `emitExpr` path". -/
private def emitLiteralAsCtor
    (aliasEnv : Std.HashMap String TSType) (targetTy : Option TSType)
    (expr : Expression) : Option LExpr := do
  let ty ← targetTy
  -- Strip parens, then expect a bare alias reference.
  let stripParenTy : TSType → TSType := fun
    | .paren inner => inner
    | other => other
  let aliasName ← match stripParenTy ty with
    | .ref n [] => some n
    | _ => none
  -- Expect the alias body to be a same-primitive literal union.
  let aliasBody ← aliasEnv[aliasName]?
  let branches ← match stripParenTy aliasBody with
    | .union bs => some bs
    | _ => none
  guard ((commonLiteralPrimitive branches).isSome)
  -- Recognize the input expression as a TSType literal.
  let exprLit : Option TSType := match expr with
    | .literal _ (.string s) _   => some (.stringLit s)
    | .literal _ (.number n) _   => some (.numberLit n)
    | .literal _ (.boolean b) _  => some (.booleanLit b)
    | .unaryExpr _ .neg _ (.literal _ (.number n) _) => some (.numberLit (-n))
    | _ => none
  let lit ← exprLit
  -- Find the matching branch by structural equality and emit `.ctor`.
  -- Lean elaborates `.«val»` against the expected inductive type.
  let matchedText ← branches.findSome? fun b =>
    if b == lit then literalCtorText b else none
  some (.ctor s!"«{matchedText}»" [])

/-- Strip `paren` wrappers (bounded — the parser only ever produces a
    finite chain). -/
private partial def stripParen : TSType → TSType
  | .paren inner => stripParen inner
  | other => other

/-- If `targetTy` is (modulo parens) a bare reference to a name registered
    in `structFields`, return that name; otherwise `none`. Anonymous object
    types and union/alias references that are not registered structures yield
    `none`, which routes the literal to the TH9005 rejection. -/
private def structNameOfTarget (env : EmitEnv) : TSType → Option String
  | .paren inner => structNameOfTarget env inner
  | .ref n []    => if env.structFields.contains n then some n else none
  | _            => none

/-- Refinement names introduced by `@thales/prelude`. These are recognized
    bare so an imported `const b: Byte = …` resolves to `.refinement .byte`
    even though the prelude bindings aren't in the local `aliasEnv` (the
    emit only sees `typeAliasDecl` for in-file aliases). -/
private def preludeRefinementName? : String → Option RefinementKind
  | "Integer" => some .integer
  | "Natural" => some .natural
  | "Byte" => some .byte
  | "Bit" => some .bit
  | _ => none

/-- Resolve a target type to a refinement kind, following one level of
    type-alias indirection through `aliasEnv`. Used to detect refinement
    targets like `Byte` (a TS alias tagged `.refinement` by the type-checker
    via the prelude shim). -/
private partial def resolveRefinementTarget
    (aliasEnv : Std.HashMap String TSType) : TSType → Option RefinementKind
  | .refinement k => some k
  | .paren inner => resolveRefinementTarget aliasEnv inner
  | .ref name [] =>
      match preludeRefinementName? name with
      | some k => some k
      | none =>
          match aliasEnv[name]? with
          | some inner => resolveRefinementTarget aliasEnv (stripParen inner)
          | none => none
  | _ => none

/-- If the target type resolves to a refinement and the expression is a
    numeric literal in range, emit `⟨lit, by native_decide⟩`. Otherwise
    return `none` and let the caller fall through to the normal expression
    path. The compile-time literal-range check is enforced by Parcel 3
    (TH0080); here we just emit the constructor wrapper. -/
private def emitRefinementLiteral
    (aliasEnv : Std.HashMap String TSType) (targetTy : Option TSType)
    (expr : Expression) : Option LExpr := do
  let ty ← targetTy
  let _ ← resolveRefinementTarget aliasEnv ty
  -- Recognize a numeric literal (or its negation).
  let litExpr : Option LExpr := match expr with
    | .literal _ (.number n) _ => some (.float n)
    | .unaryExpr _ .neg _ (.literal _ (.number n) _) => some (.float (-n))
    | _ => none
  let v ← litExpr
  some (.anonCtor [v] "by native_decide")

/-- Wrap a return expression in `.some` when the expected return type is `Option T`.
    If the expression is already `.none` (null literal) or refers to the bare
    `undefined` identifier, leave it as `.none`. Optional-typed accessors
    (`arr[k]?`, `Thales.TS.indexRead`) already produce `Option T` and are
    passed through. Otherwise wrap in `.some`. -/
private def wrapReturn (retTy : Option TSType) (e : LExpr) : LExpr :=
  match retTy with
  | some (.option _) =>
    match e with
    | .ctor "none" [] => e
    | .var "undefined" => .ctor "none" []
    | .indexOpt _ _ => e
    | .app (.var "Thales.TS.indexRead") _ => e
    | other => .ctor "some" [other]
  | _ => e

/-- Right-associative `LType.sum` chain over the throws list:
    `[A, B, C] → A ⊕ (B ⊕ C)`. -/
private def buildErrorType (throwTypes : List String) : Option LType :=
  match throwTypes with
  | [] => none
  | [t] => some (.const t)
  | _ =>
    let rec go : List String → LType
      | []  => .const "(unreachable)"
      | [t] => .const t
      | t :: rest => .sum (.const t) (go rest)
    some (go throwTypes)

/-- Sum injection for a thrown value at `idx` of `n` throw types. -/
private def buildInjection (n : Nat) (idx : Nat) (val : LExpr) : LExpr :=
  if n == 1 then val
  else
    let isLast := idx == n - 1
    let innerVal : LExpr := if isLast then val else .ctor "inl" [val]
    let rec applyInr : Nat → LExpr → LExpr
      | 0, e => e
      | k + 1, e => .ctor "inr" [applyInr k e]
    applyInr idx innerVal

private def buildExceptRetTy (throwTypes : List String) (retTy : LType) : LType :=
  match buildErrorType throwTypes with
  | none => retTy
  | some errTy => .app "Except" [errTy, retTy]

/-- True when an arithmetic binary operator wants its operands as plain `Float`
    (so refinement-typed identifiers need an explicit `.val` projection). The
    relational operators are listed too — `i < xs.length` after `xs.length`
    became `Natural` would otherwise hit a missing `LT Float Natural`. -/
private def arithBinaryOp : BinaryOperator → Bool
  | .add | .sub | .mul | .div | .mod | .exp
  | .lt | .leq | .gt | .geq
  | .bitor | .bitxor | .bitand | .shl | .shr | .ushr => true
  | _ => false

/-- Equality operators (`===`/`!==`/`==`/`!=`). When one operand is a
    refinement-typed identifier (e.g. comparing `b === 0` with `b : Bit`),
    the operand is `.val`-projected so the comparison elaborates as
    `Float == Float` rather than `Bit == Float` (which would need an
    impossible `OfScientific Bit`). `coerceToFloat` only projects genuine
    refinement bindings, so string/boolean/discriminant equalities are
    unaffected. -/
private def eqBinaryOp : BinaryOperator → Bool
  | .eq | .neq | .seq | .sneq => true
  | _ => false

/-- True when the named binding holds a refinement-typed value, so an
    `.identifier` expression referring to it should be projected via
    `.val` in arithmetic contexts. -/
private def isRefinementBinding (env : EmitEnv) (name : String) : Bool :=
  match env.bindingEnv.get? name with
  | some (.refinement _) => true
  | some (.ref tyName []) =>
      (preludeRefinementName? tyName).isSome ||
      (match env.aliasEnv[tyName]? with
       | some inner => match stripParen inner with
           | .refinement _ => true
           | _ => false
       | none => false)
  | _ => false

/-- Project `.val` off an identifier if it refers to a refinement-typed
    binding; otherwise return the expression unchanged. Used to lower
    arithmetic on refinement operands to the underlying `Float`. -/
private def coerceToFloat (env : EmitEnv) (e : Expression) (rendered : LExpr) : LExpr :=
  match e with
  | .identifier _ name =>
      if isRefinementBinding env name then .proj rendered "val" else rendered
  | _ => rendered

/-- Detect the prelude refinement-narrowing predicates `isInteger(x)`,
    `isNatural(x)`, `isByte(x)`, `isBit(x)`, and `Number.isSafeInteger(x)`
    (the latter is treated as `isInteger`). Returns the var name being
    narrowed and the kind it gets refined to.

    Also handles `&&` chains: `isInteger(x) && isNatural(x) && isByte(x)` is
    recognised as narrowing `x` to the most-specific kind across the chain
    (highest `RefinementKind.rank`), provided every leaf tests the same variable.
    Mixed-variable conjunctions return `none`. -/
private def detectRefinementPredicate : Expression → Option (String × RefinementKind)
  | .callExpr _ (.identifier _ "isInteger") [.identifier _ v] _ => some (v, .integer)
  | .callExpr _ (.identifier _ "isNatural") [.identifier _ v] _ => some (v, .natural)
  | .callExpr _ (.identifier _ "isByte") [.identifier _ v] _ => some (v, .byte)
  | .callExpr _ (.identifier _ "isBit") [.identifier _ v] _ => some (v, .bit)
  | .callExpr _ (.memberExpr _ (.identifier _ "Number") (.identifier _ "isSafeInteger") false _)
              [.identifier _ v] _ =>
      some (v, .integer)
  -- `&&` conjunction: both sides must narrow the same variable; return the
  -- most-specific kind (highest rank = lowest in the inclusion chain).
  | .logicalExpr _ .«and» left right =>
      match detectRefinementPredicate left, detectRefinementPredicate right with
      | some (lv, lk), some (rv, rk) =>
          if lv == rv then
            -- Pick the kind with the higher rank (more specific).
            some (lv, if lk.rank ≥ rk.rank then lk else rk)
          else none
      | _, _ => none
  | _ => none

/-- Map a refinement kind to the runtime predicate name (used by both the
    refinement Subtype's witness type and the dite condition). -/
private def refinementKindPredicate : RefinementKind → String
  | .integer => "isInteger"
  | .natural => "isNatural"
  | .byte => "isByte"
  | .bit => "isBit"

/-- Loud do-mode failure marker: renders as invalid Lean (same pattern as
    the pure path's `(unsupported: throw without @throws)`), so a statement
    `emitBodyDo` cannot lower breaks the build instead of being silently
    dropped. `SubsetCheck`'s `doModeLowerable` gate should make this
    unreachable; reaching it means the two have drifted. -/
private def unloweredDoStmt : List LDoStmt :=
  [.ret (.unsupported "statement not lowerable in do-mode")]

/-- Unwrap a block into its statement list; a single statement becomes a
    singleton list. -/
private def blockStmts : Statement → List Statement
  | .blockStmt _ ss => ss
  | other => [other]

/-- Normalize a TSType for use in emission: convert nullable unions to `option`. -/
private def normalizeForEmit : TSType → TSType
  | .union types =>
    match normalizeNullableUnion types with
    | some optTy => optTy
    | none => .union types
  | other => other

/-- The binding is recorded and resolves to something other than `Option`.
    Null-test lowering keeps the plain conditional only in this case: when a
    null/undefined-tested binding has NO recorded type (e.g. an element read
    off a contextually-typed callback parameter), it is still nullable in any
    program both checkers accept, hence `Option`-typed in the emitted Lean —
    so the narrowing match is safe to emit without an entry. -/
private def knownNonOptionBinding (env : EmitEnv) (name : String) : Bool :=
  match env.bindingEnv.get? name with
  | some ty =>
      match normalizeForEmit (resolveTypeAlias env ty) with
      | .option _ => false
      | _ => true
  | none => false

/-- Match arms for a lowered null/undefined test, ordered by test polarity:
    a positive test (`x === null`) puts the THEN body on the none arm; a
    negated one (`x !== null`, #43) puts it on the some arm. The some arm
    rebinds `name` at the narrowed type via pattern shadowing. Shared by the
    pure (`emitBodyEnv`) and do-mode (`emitBodyDo`) lowerings. -/
private def nullTestArms {β : Type} (name : String) (positive : Bool)
    (thnBody otherBody : β) : List (LPattern × β) :=
  let someArm := LPattern.ctor "some" [.var name]
  let noneArm := LPattern.ctor "none" []
  if positive then [(noneArm, thnBody), (someArm, otherBody)]
  else [(someArm, thnBody), (noneArm, otherBody)]

/-- Infer `number[]`/`string[]` from a homogeneous array literal — every
    element a numeric, or every element a string, literal. Returns `none` for an
    empty, mixed, or non-literal-element array, so callers keep their
    conservative fallback. Mirrors tsc's element-type inference for the cases
    the emitter can lower (#70). -/
private def arrayLiteralType? (elems : List (Option Expression)) : Option TSType :=
  if elems.isEmpty then none
  else if elems.all (fun | some (.literal _ (.number _) _) => true | _ => false) then
    some (.array .number)
  else if elems.all (fun | some (.literal _ (.string _) _) => true | _ => false) then
    some (.array .string)
  else none

/-- Record a declarator's binding type in `env.bindingEnv`: the normalized
    annotation when present, else a type inferred from the initializer shape
    (call to a declared function / element read on a typed array binding /
    homogeneous array literal).
    Shared by `emitVarDecl` and `emitVarDeclDo` so the pure and do-mode
    paths cannot drift. -/
private def recordDeclBinding (env : EmitEnv) (name : String)
    (typeAnnotation : Option TSType) (init : Option Expression) : EmitEnv :=
  let inferredTy : Option TSType := match init with
    | some (.callExpr _ (.identifier _ f) _ _) => env.funcRetTypes.get? f
    | some (.newExpr _ (.identifier _ c) _) =>
        if env.classCtorParams.contains c then some (.ref c []) else none
    | some (.memberExpr _ (.identifier _ arrName) _ true _) =>
        (arrayElemTy? env arrName).map (fun et => TSType.option et)
    -- Literal initializers carry a knowable non-Option primitive type
    -- (the smallest slice of RHS inference; #61 generalizes the rest).
    | some (.literal _ (.string _) _)  => some .string
    | some (.literal _ (.number _) _)  => some .number
    | some (.literal _ (.bigint _) _)  => some .bigint
    | some (.literal _ (.boolean _) _) => some .boolean
    | some (.arrayExpr _ elems) => arrayLiteralType? elems
    | _ => none
  match (typeAnnotation.map normalizeForEmit) <|> inferredTy with
  | some t => { env with bindingEnv := env.bindingEnv.insert name t }
  | none   => env

mutual

/-- Translate a JS `Expression` to a Lean `LExpr`. Unsupported constructs
    emit `.unsupported "expression"`; SubsetCheck rejects them upstream.
    `env` carries the binding-type table so refinement-typed identifiers
    can be `.val`-projected when used in arithmetic. -/
partial def emitExprEnv (env : EmitEnv) : Expression → LExpr
  -- Literals
  | .literal _ (.number n) _ => .float n
  | .literal _ (.bigint n) _ => .int n
  | .literal _ (.string s) _ => .str s
  | .literal _ (.boolean b) _ => .bool b
  | .literal _ .null _       => .ctor "none" []
  | .literal _ (.regex _ _) _ => .unsupported "regex literal"
  -- Identifier. The JS numeric globals `NaN`/`Infinity` are `number`-typed but
  -- have no bare Lean counterpart, so lower them to the runtime `Float`
  -- constants (`-Infinity` lowers as the negation of `Infinity`).
  | .identifier _ "NaN"      => .var "tsNaN"
  | .identifier _ "Infinity" => .var "tsInfinity"
  | .identifier _ name => .var name
  -- Binary expressions — null-equality checks emit isNone/isSome on Option values
  -- `x === null` / `x === undefined` (and reverses, with `==` too) → x.isNone
  | .binaryExpr _ .seq (.identifier _ varName) (.literal _ .null _)
  | .binaryExpr _ .eq  (.identifier _ varName) (.literal _ .null _)
  | .binaryExpr _ .seq (.literal _ .null _)    (.identifier _ varName)
  | .binaryExpr _ .eq  (.literal _ .null _)    (.identifier _ varName)
  | .binaryExpr _ .seq (.identifier _ varName) (.identifier _ "undefined")
  | .binaryExpr _ .eq  (.identifier _ varName) (.identifier _ "undefined")
  | .binaryExpr _ .seq (.identifier _ "undefined") (.identifier _ varName)
  | .binaryExpr _ .eq  (.identifier _ "undefined") (.identifier _ varName) =>
      -- A definedness test on a recorded non-Option binding is vacuous:
      -- `x === null`/`=== undefined` is always false. Fold so we never
      -- emit `.isNone` on a non-Option value (which does not elaborate).
      if knownNonOptionBinding env varName then .bool false
      else .proj (.var varName) "isNone"
  -- `x !== null` / `x !== undefined` (and reverses, with `!=` too) → x.isSome
  | .binaryExpr _ .sneq (.identifier _ varName) (.literal _ .null _)
  | .binaryExpr _ .neq  (.identifier _ varName) (.literal _ .null _)
  | .binaryExpr _ .sneq (.literal _ .null _)    (.identifier _ varName)
  | .binaryExpr _ .neq  (.literal _ .null _)    (.identifier _ varName)
  | .binaryExpr _ .sneq (.identifier _ varName) (.identifier _ "undefined")
  | .binaryExpr _ .neq  (.identifier _ varName) (.identifier _ "undefined")
  | .binaryExpr _ .sneq (.identifier _ "undefined") (.identifier _ varName)
  | .binaryExpr _ .neq  (.identifier _ "undefined") (.identifier _ varName) =>
      -- `x !== null`/`!== undefined` is always true for a recorded
      -- non-Option binding. Fold (see the `isNone` arm above).
      if knownNonOptionBinding env varName then .bool true
      else .proj (.var varName) "isSome"
  -- General binary expressions: when the op is arithmetic, relational, or
  -- equality, project `.val` off any refinement-typed identifier operands
  -- so the operation elaborates on plain `Float`. `%`, bitwise, and shift
  -- ops route through JS-semantics runtime helpers (#32) — bare Lean
  -- operators have no Float instances (and the wrong semantics anyway).
  | .binaryExpr _ op left right =>
      let lExpr := emitExprEnv env left
      let rExpr := emitExprEnv env right
      match jsBinopHelper op with
      | some helper =>
          .app (.var helper) [coerceToFloat env left lExpr, coerceToFloat env right rExpr]
      | none =>
        if arithBinaryOp op || eqBinaryOp op then
          .binOp (binaryOpStr op) (coerceToFloat env left lExpr) (coerceToFloat env right rExpr)
        else
          .binOp (binaryOpStr op) lExpr rExpr
  -- Logical expressions
  | .logicalExpr _ .«and» left right =>
      .binOp "&&" (emitExprEnv env left) (emitExprEnv env right)
  | .logicalExpr _ .«or» left right =>
      .binOp "||" (emitExprEnv env left) (emitExprEnv env right)
  -- Nullish coalescing `x ?? y` → `x.getD y`
  | .logicalExpr _ .nullishCoalesce left right =>
      .app (.proj (emitExprEnv env left) "getD") [emitExprEnv env right]
  -- Unary expressions
  | .unaryExpr _ .neg _ arg =>
      let r := emitExprEnv env arg
      .app (.var "Neg.neg") [coerceToFloat env arg r]
  | .unaryExpr _ .pos _ arg => emitExprEnv env arg
  | .unaryExpr _ .not _ arg => .app (.var "not") [emitExprEnv env arg]
  | .unaryExpr _ .bitnot _ arg => .app (.var "Complement.complement") [emitExprEnv env arg]
  | .unaryExpr _ _ _ _ => .unsupported "unary op"
  -- Update (++/--): SubsetCheck rejects; placeholder
  | .updateExpr _ _ _ _ => .unsupported "update expr"
  -- Conditional (ternary). A null/undefined-guard on an Option-typed
  -- binding lowers to the narrowing match (the expression twin of the
  -- `ifStmt` lowering in `emitBodyEnv`/`emitBodyDo`): the non-nullish arm
  -- rebinds the name at the unwrapped type, so narrowed reads like `o.v`
  -- project the payload rather than the Option (#133). Known non-Option
  -- bindings keep the plain ite — their test already folds to a constant.
  | .conditionalExpr _ cond thn els =>
      match nullCheckVar cond with
      | some (varName, positive) =>
          if knownNonOptionBinding env varName then
            .ite (emitExprEnv env cond) (emitExprEnv env thn) (emitExprEnv env els)
          else
            .match_ (.var varName)
              (nullTestArms varName positive (emitExprEnv env thn) (emitExprEnv env els))
      | none =>
          .ite (emitExprEnv env cond) (emitExprEnv env thn) (emitExprEnv env els)
  -- Call expression. When the callee is a known function whose parameters
  -- are refinement-typed, wrap matching numeric-literal args in Subtype
  -- constructors. Without this the parser-stripped `1 as Natural` would
  -- emit as a bare `1.0` and Lean would fail to elaborate `Float ≠ Natural`.
  -- Also dispatches `Math.abs(integer)` → `Math.absI` so the result type
  -- is `Natural`, matching the TS overload in `Builtins.lean`.
  | .callExpr _ callee args _ =>
      -- Math.abs overload dispatch.
      match callee, args with
      | .memberExpr _ (.identifier _ "Math") (.identifier _ "abs") false _, [arg] =>
          let argRendered := emitExprEnv env arg
          let isInt : Bool := match arg with
            | .identifier _ n => isRefinementBinding env n
            | _ => false
          if isInt then
            .app (.var "Math.absI") [argRendered]
          else
            .app (.var "Math.abs") [argRendered]
      -- `xs.reduce(cb, init)` → Lean `xs.foldl cb init` (built-in
      -- `Array.foldl` has `(f) (init)` order, matching TS's
      -- `(callback, initialValue)`). The runtime `Array.reduce` helper has
      -- the opposite order and must NOT be used here.
      | .memberExpr _ obj (.identifier _ "reduce") false _, [cb, initArg] =>
          .app (.proj (emitExprEnv env obj) "foldl")
            [emitExprEnv env cb, emitExprEnv env initArg]
      | _, _ =>
      -- #28: array-method overrides. `xs.join/indexOf/includes(...)` on an
      -- identifier receiver recorded as `number[]`/`string[]`. Non-identifier
      -- receivers are rejected earlier by TH0085, so they never reach here;
      -- unsupported element types fall through to the generic emission below
      -- (a Lean compile error if ever exercised — never a silent miscompile).
      let arrayMethodOverride : Option LExpr :=
        match callee with
        | .memberExpr _ (.identifier _ recv) (.identifier _ m) false _ =>
            let elemTy? := env.bindingEnv.get? recv
            let firstArg? : Option LExpr := match args with
              | a :: _ => some (emitExprEnv env a)
              | [] => none
            -- #67: indexOf/includes accept an optional `fromIndex`. When present
            -- it routes to the `…From` runtime helper; otherwise the
            -- single-argument helper. `join`'s second argument is not part of
            -- the subset, so it ignores anything past the separator.
            let secondArg? : Option LExpr := match args with
              | _ :: b :: _ => some (emitExprEnv env b)
              | _ => none
            let indexOfExpr : LExpr → LExpr := fun a =>
              match secondArg? with
              | some b => .app (.var "Array.indexOfFromJS") [.var recv, a, b]
              | none   => .app (.var "Array.indexOfJS") [.var recv, a]
            let includesExpr : String → LExpr → LExpr := fun helper a =>
              match secondArg? with
              | some b => .app (.var (helper ++ "From")) [.var recv, a, b]
              | none   => .app (.var helper) [.var recv, a]
            -- lastIndexOf mirrors indexOf's optional-fromIndex routing.
            let lastIndexOfExpr : LExpr → LExpr := fun a =>
              match secondArg? with
              | some b => .app (.var "Array.lastIndexOfFromJS") [.var recv, a, b]
              | none   => .app (.var "Array.lastIndexOfJS") [.var recv, a]
            -- some/every/findIndex take a predicate (the first argument) and
            -- lower to the generic Lean primitives `Array.any`/`Array.all` and
            -- the `Array.findIndexJS` helper. Element type is irrelevant to
            -- these, but the receiver is still resolved to number[]/string[]
            -- so unlowerable shapes are rejected (TH0085) rather than emitted.
            let predExpr : String → LExpr → LExpr := fun helper cb =>
              .app (.var helper) [.var recv, cb]
            match elemTy?, m with
            | some (.array .number), "join" =>
                some (.app (.var "Array.joinJS") [.var recv, firstArg?.getD (.str ",")])
            | some (.array .string), "join" =>
                some (.app (.var "Array.joinJS") [.var recv, firstArg?.getD (.str ",")])
            | some (.array .number), "indexOf" =>
                firstArg?.map indexOfExpr
            | some (.array .string), "indexOf" =>
                firstArg?.map indexOfExpr
            | some (.array .number), "includes" =>
                firstArg?.map (includesExpr "Array.includesFloat")
            | some (.array .string), "includes" =>
                firstArg?.map (includesExpr "Array.includesStr")
            | some (.array .number), "lastIndexOf" =>
                firstArg?.map lastIndexOfExpr
            | some (.array .string), "lastIndexOf" =>
                firstArg?.map lastIndexOfExpr
            | some (.array .number), "some" =>
                firstArg?.map (predExpr "Array.any")
            | some (.array .string), "some" =>
                firstArg?.map (predExpr "Array.any")
            | some (.array .number), "every" =>
                firstArg?.map (predExpr "Array.all")
            | some (.array .string), "every" =>
                firstArg?.map (predExpr "Array.all")
            | some (.array .number), "findIndex" =>
                firstArg?.map (predExpr "Array.findIndexJS")
            | some (.array .string), "findIndex" =>
                firstArg?.map (predExpr "Array.findIndexJS")
            | _, _ => none
        | _ => none
      match arrayMethodOverride with
      | some e => e
      | none =>
      let calleeFnName : Option String := match callee with
        | .identifier _ name => some name
        | _ => none
      let paramTys : List (Option TSType) := match calleeFnName with
        | some n => match env.funcParamTypes.get? n with
            | some tys => tys.map some ++ List.replicate (args.length - tys.length) none
            | none => List.replicate args.length none
        | none => List.replicate args.length none
      let coerceArg : Expression → Option TSType → LExpr := fun a tyOpt =>
        emitExprWithExpectedTy env tyOpt a
      let coercedArgs : List LExpr := List.zipWith coerceArg args paramTys
      .app (emitExprEnv env callee) coercedArgs
  -- Member expression
  -- `Number.isSafeInteger` → Float.isSafeInteger; `Number.isInteger` →
  -- Float.isInteger (the JS-mathematical sense). These map JS's static
  -- `Number` namespace methods to Lean's Float helpers.
  | .memberExpr _ (.identifier _ "Number") (.identifier _ "isSafeInteger") false _ =>
      .var "Float.isSafeInteger"
  | .memberExpr _ (.identifier _ "Number") (.identifier _ "isInteger") false _ =>
      .var "Float.isInteger"
  | .memberExpr _ (.identifier _ "Number") (.identifier _ "isNaN") false _ =>
      .var "isNaN"
  -- `Math.abs` and other Math static methods. The Lean side uses
  -- `Float.abs`. For refinement-typed args (Integer → Natural), the value
  -- flows via the Coe lattice.
  | .memberExpr _ (.identifier _ "Math") (.identifier _ "abs") false _ =>
      .var "Math.abs"
  | .memberExpr _ (.identifier _ "Math") (.identifier _ "floor") false _ =>
      .var "Math.floor"
  | .memberExpr _ (.identifier _ "Math") (.identifier _ "ceil") false _ =>
      .var "Math.ceil"
  | .memberExpr _ (.identifier _ "Math") (.identifier _ "round") false _ =>
      .var "Math.round"
  | .memberExpr _ (.identifier _ "Math") (.identifier _ "sqrt") false _ =>
      .var "Math.sqrt"
  | .memberExpr _ (.identifier _ "Math") (.identifier _ "min") false _ =>
      .var "Math.min"
  | .memberExpr _ (.identifier _ "Math") (.identifier _ "max") false _ =>
      .var "Math.max"
  -- `arr.length` lowers to `Array.toNaturalSize arr` (a `Natural`); the Coe
  -- chain lets it flow into Float slots. `s.length` lowers to
  -- `String.toNaturalLength s`. Inside `dite`-rewritten conditions, the
  -- caller (`emitCondForDite`) bypasses this and uses `arr.size` directly.
  | .memberExpr _ (.identifier _ arrName) (.identifier _ "length") false _ =>
      match env.bindingEnv.get? arrName with
      | some (.array _) | some (.tuple _) =>
          .app (.var "Array.toNaturalSize") [.var arrName]
      | some (.string) =>
          .app (.var "String.toNaturalLength") [.var arrName]
      | some other =>
          -- A receiver bound to a known structure (interface or class) with a
          -- declared `length` field reads it as a plain projection; the
          -- `.toFloat` fallback would mistype e.g. an Int-valued field (#106).
          match resolveTypeAlias env other with
          | .ref n [] =>
              if env.structFields.contains n then .proj (.var arrName) "length"
              else .proj (.proj (.var arrName) "length") "toFloat"
          | _ => .proj (.proj (.var arrName) "length") "toFloat"
      | none =>
          -- Unknown binding: best-effort `s.length.toFloat`.
          .proj (.proj (.var arrName) "length") "toFloat"
  -- `this.<f>`: in ctor mode the field-local `let f` binding; in a method
  -- a projection off the receiver (#106)
  | .memberExpr _ (.thisExpr tb) (.identifier _ propName) false _ =>
      if env.ctorMode then .var propName
      else .proj (emitExprEnv env (.thisExpr tb)) propName
  | .memberExpr _ obj (.identifier _ propName) false _ =>
      .proj (emitExprEnv env obj) propName
  | .memberExpr _ obj idx true _ =>
      -- `xs[i]`: JS-semantics element read; the index stays a Float and the
      -- result is `Option α` (TS `T | undefined` under noUncheckedIndexedAccess).
      -- A refinement-typed index (e.g. Natural) projects to its underlying Float.
      let idxL := coerceToFloat env idx (emitExprEnv env idx)
      .app (.var "Thales.TS.indexRead") [emitExprEnv env obj, idxL]
  | .memberExpr _ obj _ _ _ =>
      .proj (emitExprEnv env obj) "(unknown)"
  -- Array expression: emit as List.toArray applied to nested cons/nil
  | .arrayExpr _ elements =>
      let exprs := elements.filterMap id |>.map (emitExprEnv env)
      .app (.var "List.toArray") [mkListLit exprs]
  -- Arrow function expression
  | .arrowFunctionExpr _ params body _ async _ =>
      if async then .unsupported "async arrow"
      else
        let leanParams := params.filterMap fun
          | .simple id => some (id.name, none)
          | .withDefault id _ => some (id.name, none)
          | .rest id => some (id.name, none)
          | .pattern _ => none
        let bodyExpr := match body with
          | .inl e     => emitExprEnv env e
          | .inr stmt  => emitBodyEnv env [stmt]
        .lam leanParams bodyExpr
  -- `this` inside a class method lowers to the receiver parameter (#106)
  | .thisExpr _ =>
      match env.thisName with
      | some n => .var n
      | none => .unsupported "this outside a class"
  -- `new C(args)` → `C.ctor' args` for local v1 classes (with expected-type
  -- direction from the ctor signature) and imported names (without, same
  -- degradation as calls to imported functions). Builtin `new` targets
  -- (`Error` etc.) keep their statement-level special cases and otherwise
  -- fall to the placeholder (#106).
  | .newExpr _ (.identifier _ cname) args =>
      match env.classCtorParams.get? cname with
      | some ctorParams =>
          let expected : List (Option TSType) :=
            ctorParams.map (fun (_, t) => some t)
              ++ List.replicate (args.length - ctorParams.length) none
          let coerced := List.zipWith (emitExprWithExpectedTy env) expected args
          .app (.proj (.var cname) "ctor'") coerced
      | none =>
          if env.importedNames.contains cname then
            .app (.proj (.var cname) "ctor'") (args.map (emitExprEnv env))
          else .unsupported "new expression"
  -- Assignment: SubsetCheck rejects; placeholder
  | .assignmentExpr _ _ _ _ => .unsupported "assignment"
  -- Object literal with a `kind: "..."` discriminator: emit as an anonymous
  -- constructor `.kindVal <other-field-values>` and let Lean resolve which
  -- inductive via context. Field values are emitted in literal order, which
  -- must match the constructor's parameter order. For non-discriminated
  -- object literals there is no clean shallow embedding in v1 — fall through
  -- to the placeholder and rely on the type checker to have rejected earlier.
  | .objectExpr _ props =>
      let regularProps := objectLiteralEntries props
      let discVal : Option String := regularProps.findSome? fun (k, v) =>
        if k == "kind" then
          match v with
          | .literal _ (.string s) _ => some s
          | _ => none
        else none
      match discVal with
      | some ctor =>
          let otherFields := regularProps.filter fun (k, _) => k != "kind"
          .ctor ctor (otherFields.map fun (_, v) => emitExprEnv env v)
      | none => .unsupported "expression"
  -- Template literal: `q0${e0}q1${e1}...qn`
  -- Emitted as string concatenation: "q0" ++ JSShow.jsShow e0 ++ "q1" ++ ...
  -- Quasis has (n+1) elements for n expressions; gaps with empty strings are skipped.
  | .templateLiteral _ quasis exprs =>
      -- Build a flat list of string pieces, alternating quasis and jsShow(expr).
      let pieces : List LExpr :=
        let qExprs := quasis.map fun q => LExpr.str q.value
        let eExprs := exprs.map fun e => LExpr.app (.var "JSShow.jsShow") [emitExprEnv env e]
        -- Interleave: q0, e0, q1, e1, ..., qn (quasis always has one more than exprs)
        let zipped := qExprs.zip eExprs  -- pairs (q0,e0), (q1,e1), ...
        let interleaved := zipped.flatMap fun (q, e) => [q, e]
        -- Append the last quasi (if quasis is longer than exprs)
        let lastQ := qExprs.getLast?
        match lastQ with
        | some last => interleaved ++ [last]
        | none => interleaved  -- unreachable: parser guarantees quasis is non-empty
      -- Remove empty string pieces to keep the output clean.
      let nonEmpty := pieces.filter fun p => match p with | .str "" => false | _ => true
      match nonEmpty with
      | [] => .str ""
      | [single] => single
      | first :: rest => rest.foldl (fun acc p => .binOp "++" acc p) first
  -- Everything else
  | _ => .unsupported "expression"

/-- Backwards-compatible wrapper used by the few sites that have no env
    available (e.g. the top-level `console.log` lowering). Calls
    `emitExprEnv` with an empty env, which means refinement detection is
    skipped — the caller must guarantee operands are `Float`-typed. -/
partial def emitExpr : Expression → LExpr := emitExprEnv {}

/-- Lower an object literal `{ … }` to a Lean structure instance when the
    target type resolves to a known structure. Field values are emitted in the
    structure's declared field order, each with its declared field type as the
    expected type (so nested record fields recurse). Returns `none` (→ caller
    falls through to `.unsupported`, then TH9005) when `expr` is not an object
    literal or the target is not a known structure. -/
partial def emitObjectLiteralAsStruct
    (env : EmitEnv) (targetTy : Option TSType) (expr : Expression) : Option LExpr := do
  let .objectExpr _ props := expr | none
  let ty ← targetTy
  let structName ← structNameOfTarget env ty
  let fields ← env.structFields[structName]?
  let provided := objectLiteralEntries props
  let fieldExprs ← fields.mapM fun (fname, fty) => do
    let v ← provided.lookup fname
    some (fname, emitExprWithExpectedTy env (some fty) v)
  some (.structLit structName fieldExprs)

/-- Lower an array literal whose element target resolves to a known structure,
    recursing element-wise with that element type. Only intercepts the
    known-structure case; all other arrays fall through to the existing
    `.arrayExpr` path in `emitExprEnv` for byte-identical output. -/
partial def emitArrayLiteralWithElemTy
    (env : EmitEnv) (targetTy : Option TSType) (expr : Expression) : Option LExpr := do
  let .arrayExpr _ elements := expr | none
  let ty ← targetTy
  let elemTy ← match stripParen ty with | .array et => some et | _ => none
  let _ ← structNameOfTarget env elemTy
  let exprs := elements.filterMap id |>.map (emitExprWithExpectedTy env (some elemTy))
  some (.app (.var "List.toArray") [mkListLit exprs])

/-- Type-directed expression emission: the single entry point for positions
    where the target type is known. Tries the literal-lowering helpers in
    priority order, then falls back to the plain `emitExprEnv`. -/
partial def emitExprWithExpectedTy
    (env : EmitEnv) (targetTy : Option TSType) (expr : Expression) : LExpr :=
  ((emitRefinementLiteral env.aliasEnv targetTy expr)
    <|> (emitLiteralAsCtor env.aliasEnv targetTy expr)
    <|> (emitObjectLiteralAsStruct env targetTy expr)
    <|> (emitArrayLiteralWithElemTy env targetTy expr))
    |>.getD (emitExprEnv env expr)

/-- Emit a list of variable declarators as nested `let` bindings.
    `env` is consulted so that initializers whose target type resolves
    to a refinement (e.g. `Byte`, `Natural`) get wrapped in a Subtype
    constructor (`⟨lit, by native_decide⟩`), and so that arithmetic on
    refinement-typed operands gets `.val`-projected. New bindings extend
    `env.bindingEnv` for subsequent declarators / the body. -/
partial def emitVarDecl (env : EmitEnv)
    (decls : List VariableDeclarator) (body : EmitEnv → LExpr) : LExpr :=
  match decls with
  | [] => body env
  | d :: rest =>
      match d with
      | .mk _ (.identifier id) init typeAnnotation =>
          let ty := typeAnnotation.map emitType
          let targetTy : Option TSType := typeAnnotation
          let initExpr := match init with
            | some e => emitExprWithExpectedTy env targetTy e
            | none   => .var "()"
          let env' := recordDeclBinding env id.name typeAnnotation init
          .letE id.name ty initExpr (emitVarDecl env' rest body)
      | _ => emitVarDecl env rest body  -- destructuring patterns skipped for v1

/-- Emit a list of statements as a Lean expression. Handles var decls, `if`,
    block, expression, `return`, and `switch` on discriminated unions. -/
partial def emitBodyEnv (env : EmitEnv) : List Statement → LExpr
  | .returnStmt _ (some e) :: _ =>
      let emitted := emitExprWithExpectedTy env env.retTy e
      let inner := wrapReturn env.retTy emitted
      if env.throwTypes.isEmpty then inner else .ctor "ok" [inner]
  | .returnStmt _ none :: _     => .var "()"
  | .variableDecl (.mk _ decls _) :: rest =>
      -- When the enclosing function has @throws and the initializer calls
      -- a @throws function, emit `match callee args with .ok x => rest | .error e => …`.
      if !env.throwTypes.isEmpty then
        match decls with
        | [.mk _ (.identifier id) (some (callExpr@(.callExpr _ (.identifier _ calleeName) _ _))) _] =>
            match env.funcThrowsEnv.get? calleeName with
            | some calledThrows =>
                let callLExpr := emitExprEnv env callExpr
                let okBodyExpr := emitBodyEnv env rest
                let okArm : LPattern × LExpr := (.ctor "ok" [.var id.name], okBodyExpr)
                let errVar := "e__prop__"
                let errExpr : LExpr :=
                  if calledThrows == env.throwTypes then
                    .ctor "error" [.var errVar]
                  else
                    match calledThrows with
                    | [singleType] =>
                        let idx := env.throwTypes.findIdx? (· == singleType) |>.getD 0
                        let n := env.throwTypes.length
                        .ctor "error" [buildInjection n idx (.var errVar)]
                    | _ => .ctor "error" [.var errVar]
                let errArm : LPattern × LExpr := (.ctor "error" [.var errVar], errExpr)
                .match_ callLExpr [okArm, errArm]
            | none => emitVarDecl env decls (fun env' => emitBodyEnv env' rest)
        | _ => emitVarDecl env decls (fun env' => emitBodyEnv env' rest)
      else
        emitVarDecl env decls (fun env' => emitBodyEnv env' rest)
  -- `if (x === null) thn else rest` with `x : Option T` becomes a match.
  | .ifStmt _ cond thn elsOpt :: rest =>
      -- Else-branch with the continuation appended: missing `else` encodes the
      -- early-return pattern, so `rest` becomes the implicit else-body.
      let elseBody : LExpr := match elsOpt with
        | some els => emitBodyEnv env (els :: rest)
        | none => emitBodyEnv env rest
      let fallback : LExpr :=
        .ite (emitExprEnv env cond) (emitBodyEnv env (thn :: rest)) elseBody
      -- Refinement-narrowing predicate: `if (isInteger(x)) { … }` becomes
      -- `if h : isInteger x = true then let x : Integer := ⟨x, h⟩ in … else …`.
      -- The shadow-let makes `x` flow at the refined type inside the body.
      match detectRefinementPredicate cond with
      | some (varName, kind) =>
          let hName := s!"h{env.diteBinderCounter}"
          let predName := refinementKindPredicate kind
          let condExpr : LExpr :=
            .binOp "=" (.app (.var predName) [.var varName]) (.bool true)
          let env' : EmitEnv :=
            { env with
                bindingEnv := env.bindingEnv.insert varName (.refinement kind),
                diteBinderCounter := env.diteBinderCounter + 1 }
          let inner := emitBodyEnv env' (thn :: rest)
          let shadowed : LExpr :=
            .letE varName (some (.const kind.name))
              (.anonCtor [.var varName] hName) inner
          .dite_ hName condExpr shadowed elseBody
      | none =>
        match nullCheckVar cond with
        | some (varName, positive) =>
            -- The THEN branch becomes its own match arm WITHOUT the
            -- continuation, so it must return on every path (the
            -- early-return idiom); otherwise control would fall out of
            -- the arm and the continuation — emitted only into the
            -- other arm — would be skipped. Non-returning branches and
            -- known non-Option bindings keep the plain-ite fallback.
            if !knownNonOptionBinding env varName
                && EscapeAnalysis.stmtsReturn [thn] then
              let thnArm := emitBodyEnv env [thn]
              .match_ (.var varName) (nullTestArms varName positive thnArm elseBody)
            else fallback
        | none => fallback
  | .blockStmt _ inner :: rest => emitBodyEnv env (inner ++ rest)
  | .exprStmt _ _ :: rest      => emitBodyEnv env rest
  | .switchStmt _ discriminant cases :: _ =>
      -- SubsetCheck (TH0041) guarantees the discriminated `ident.field`
      -- shape with all-return arms, so the code after the switch is dead
      -- and a fallback that DROPS the switch is never correct — the
      -- unresolved cases render the loud marker instead (#44).
      let unlowered : LExpr := .unsupported "switch not lowerable"
      match discriminant with
      | .memberExpr _ (.identifier _ scrutName) (.identifier _ _fieldName) false _ =>
          match env.bindingEnv.get? scrutName with
          | none => unlowered
          | some rawTy =>
              let resolvedTy := resolveTypeAlias env rawTy
              match resolvedTy with
              | .union branches =>
                  match asDiscriminated branches with
                  | none => unlowered
                  | some ctors =>
                      let arms : List (LPattern × LExpr) := cases.filterMap fun
                        | .mk _ (some (.literal _ (.string caseLit) _)) caseBody =>
                            match ctors.find? (fun (ctorName, _) => ctorName == caseLit) with
                            | none => none
                            | some (_ctorName, fields) =>
                                let fieldNames := fields.map (·.1)
                                let pat : LPattern :=
                                  .ctor caseLit (fieldNames.map .var)
                                let substBody := caseBody.map (substMemberAccessStmt scrutName)
                                let bodyExpr := emitBodyEnv env substBody
                                some (pat, bodyExpr)
                        | _ => none
                      -- A `default` arm lowers as the wildcard arm (#44; it
                      -- used to render `unreachable!`, a runtime panic on
                      -- any uncovered constructor). Its body gets no field
                      -- substitution — there is no single-constructor
                      -- context — so field references in it fail loudly.
                      let defaultBody? := cases.findSome? fun
                        | .mk _ none ss => some ss
                        | _ => none
                      let allArms :=
                        if arms.length >= ctors.length then arms
                        else
                          let wild : LExpr := match defaultBody? with
                            | some ss => emitBodyEnv env ss
                            | none => .var "unreachable!"
                          arms ++ [(.wildcard, wild)]
                      .match_ (.var scrutName) allArms
              | _ => unlowered
      | _ => unlowered
  | .throwStmt _ arg :: _ =>
      if env.throwTypes.isEmpty then
        -- SubsetCheck already flagged TH0060.
        .unsupported "throw without @throws"
      else
        -- Heuristic: `new E(args)` thrown at index `idx` of `@throws`.
        let thrownTypeName : String := match arg with
          | .newExpr _ (.identifier _ name) _ => name
          | _ => ""
        let idx := env.throwTypes.findIdx? (· == thrownTypeName) |>.getD 0
        -- Fully-qualified `Thales.TS.E.mk msg` to avoid ambiguity inside `Except`.
        let errorVal : LExpr := match arg with
          | .newExpr _ (.identifier _ name) [msgArg] =>
              .app (.var s!"Thales.TS.{name}.mk") [emitExprEnv env msgArg]
          | .newExpr _ (.identifier _ name) [] =>
              .var s!"(Thales.TS.{name}.mk \"\")"
          | other => emitExprEnv env other
        let n := env.throwTypes.length
        let injected := buildInjection n idx errorVal
        .ctor "error" [injected]
  -- try/catch desugars to a match on the called function's `Except` result.
  -- Two shapes are supported: a single `return f(args)` body, and a `const x =
  -- f(args)` followed by further statements. `f` must be `@throws`-annotated.
  | .tryStmt _ tryBlock (some (CatchClause.mk _ paramOpt handlerBody _catchType)) _finalizer :: outerRest =>
      let tryStmts := match tryBlock with
        | .blockStmt _ stmts => stmts
        | other => [other]
      let catchVar : String := match paramOpt with
        | some (.identifier id) => id.name
        | _ => "e__"
      let catchBodyExpr := emitBodyEnv env (match handlerBody with
        | .blockStmt _ stmts => stmts ++ outerRest
        | other => [other] ++ outerRest)
      match tryStmts with
      | [.returnStmt _ (some callExpr)] =>
          match callExpr with
          | .callExpr _ (.identifier _ fname) _ _ =>
              match env.funcThrowsEnv.get? fname with
              | some _calledThrows =>
                  let callLExpr := emitExprEnv env callExpr
                  let okVar := "v__"
                  let okResult : LExpr :=
                    if env.throwTypes.isEmpty
                    then wrapReturn env.retTy (.var okVar)
                    else .ctor "ok" [wrapReturn env.retTy (.var okVar)]
                  let okArm : LPattern × LExpr := (.ctor "ok" [.var okVar], okResult)
                  let errArm : LPattern × LExpr := (.ctor "error" [.var catchVar], catchBodyExpr)
                  .match_ callLExpr [okArm, errArm]
              | none => emitBodyEnv env (tryStmts ++ outerRest)
          | _ => emitBodyEnv env (tryStmts ++ outerRest)
      | (.variableDecl (.mk _ [.mk _ (.identifier id) (some callExpr) _] _)) :: moreStmts =>
          match callExpr with
          | .callExpr _ (.identifier _ fname) _ _ =>
              match env.funcThrowsEnv.get? fname with
              | some _calledThrows =>
                  let callLExpr := emitExprEnv env callExpr
                  let okBodyExpr := emitBodyEnv env (moreStmts ++ outerRest)
                  let okArm : LPattern × LExpr := (.ctor "ok" [.var id.name], okBodyExpr)
                  let errArm : LPattern × LExpr := (.ctor "error" [.var catchVar], catchBodyExpr)
                  .match_ callLExpr [okArm, errArm]
              | none => emitBodyEnv env (tryStmts ++ outerRest)
          | _ => emitBodyEnv env (tryStmts ++ outerRest)
      | _ => emitBodyEnv env (tryStmts ++ outerRest)
  | .tryStmt _ tryBlock none _finalizer :: outerRest =>
      let tryStmts := match tryBlock with
        | .blockStmt _ stmts => stmts
        | other => [other]
      emitBodyEnv env (tryStmts ++ outerRest)
  | _ :: rest                  => emitBodyEnv env rest
  | []                         => .var "()"

partial def emitBody : List Statement → LExpr :=
  emitBodyEnv {}

/-- #24/#25 do-mode lowering: the body of a function with an eligible
    statement-position mutation, as a list of `Id.run do` statements.
    Only shapes SubsetCheck admits into do-mode arrive here — straight-line
    mutation, declarations, `return`, `if`/`else`, discriminated-union
    switches, `for-of` and canonical `for` loops, and unlabeled
    `break`/`continue` (#25); anything else was rejected upstream
    (TH0001/TH0005/TH0006/TH0007/TH0010 …). A statement this function has
    no lowering for renders the loud `(unsupported: …)` marker — invalid
    Lean — rather than being dropped: silent divergence from the TS
    behavior is the one failure mode the conformance harness can't catch
    when the emitted file still compiles. -/
partial def emitBodyDo (env : EmitEnv) (info : EscapeAnalysis.MutationInfo)
    : List Statement → List LDoStmt
  | .returnStmt _ (some e) :: _ =>
      let emitted := emitExprWithExpectedTy env env.retTy e
      [.ret (wrapReturn env.retTy emitted)]
  | .returnStmt _ none :: _ => [.ret (.var "()")]
  | .variableDecl (.mk _ decls _) :: rest =>
      emitVarDeclDo env info decls rest
  -- `x = e` / `x OP= e`: compound forms desugar to `x := x OP e` so emission
  -- reuses the binary-op lowering (refinement projection, string concat, …).
  | .exprStmt _ (.assignmentExpr b op (.identifier _ name) rhs) :: rest =>
      let value : LExpr :=
        match op.compoundToBinary with
        | some binOp =>
            emitExprEnv env (.binaryExpr b binOp (.identifier b name) rhs)
        | none => emitExprEnv env rhs   -- plain `=` (logical never reaches do-mode)
      .assign name value :: emitBodyDo env info rest
  -- `x++` / `x--` desugar to `x := x ± 1`.
  | .exprStmt _ (.updateExpr b op (.identifier _ name) _) :: rest =>
      let one : Expression := .literal b (.number 1) "1"
      let binOp : BinaryOperator := match op with
        | .inc => .add
        | .dec => .sub
      .assign name (emitExprEnv env (.binaryExpr b binOp (.identifier b name) one))
        :: emitBodyDo env info rest
  | .blockStmt _ inner :: rest => emitBodyDo env info (inner ++ rest)
  -- `if`/`else` in statement position: branches lower WITHOUT the
  -- continuation appended (do-notation gives statement semantics — the
  -- pure path's continuation-into-branches trick at `emitBodyEnv` does
  -- not apply), so mutation inside a branch stays visible after it and
  -- `return` inside a branch is do-notation's native early return.
  | .ifStmt _ cond thn elsOpt :: rest =>
      let thnDo := emitBodyDo env info (blockStmts thn)
      let elsDo := match elsOpt with
        | some els => emitBodyDo env info (blockStmts els)
        | none => []
      -- Definedness test on an Option-typed binding: a statement-position
      -- match rebinds the name at the unwrapped type (do-mode twin of
      -- `emitBodyEnv`'s lowering). A THEN branch that returns on every
      -- path puts the continuation in the other arm, at the post-test
      -- type; otherwise the continuation follows the match.
      let narrowedMatch : Option (List LDoStmt) :=
        match nullCheckVar cond with
        | some (varName, positive) =>
            if knownNonOptionBinding env varName then none
            else if EscapeAnalysis.stmtsReturn [thn] then
              let contDo := elsDo ++ emitBodyDo env info rest
              some [.matchDo (.var varName) (nullTestArms varName positive thnDo contDo)]
            else
              some (.matchDo (.var varName) (nullTestArms varName positive thnDo elsDo)
                      :: emitBodyDo env info rest)
        | none => none
      match narrowedMatch with
      | some stmts => stmts
      | none =>
          .ifDo (emitExprEnv env cond) thnDo elsDo :: emitBodyDo env info rest
  | .exprStmt _ _ :: rest => emitBodyDo env info rest  -- dropped, as in pure mode
  -- Discriminated-union switch, do-mode twin of `emitBodyEnv`'s arm.
  -- EscapeAnalysis guarantees every arm returns and there is no `default`
  -- (`hasUnloweredSwitchShape` keeps anything else out of do-mode), so
  -- `rest` after the switch is dead code and is dropped.
  | .switchStmt _ discriminant cases :: _ =>
      -- `hasUnloweredSwitchShape` guarantees the `ident.field` discriminant
      -- shape with all-return arms and no `default`, so `rest` is dead code
      -- and a fallback that DROPS the switch is never correct — the
      -- non-discriminated cases render the loud marker instead.
      match discriminant with
      | .memberExpr _ (.identifier _ scrutName) (.identifier _ _fieldName) false _ =>
          (match env.bindingEnv.get? scrutName with
          | some rawTy =>
            (match resolveTypeAlias env rawTy with
            | .union branches =>
              (match asDiscriminated branches with
              | some ctors =>
                  let arms : List (LPattern × List LDoStmt) := cases.filterMap fun
                    | .mk _ (some (.literal _ (.string caseLit) _)) caseBody =>
                        (match ctors.find? (fun (ctorName, _) => ctorName == caseLit) with
                        | some (_ctorName, fields) =>
                            let fieldNames := fields.map (·.1)
                            let pat : LPattern := .ctor caseLit (fieldNames.map .var)
                            let substBody := caseBody.map (substMemberAccessStmt scrutName)
                            some (pat, emitBodyDo env info substBody)
                        | none => none)
                    | _ => none
                  let allArms :=
                    if arms.length >= ctors.length then arms
                    else arms ++ [(.wildcard, [.ret (.var "unreachable!")])]
                  [.matchDo (.var scrutName) allArms]
              | none => unloweredDoStmt)
            | _ => unloweredDoStmt)
          | none => unloweredDoStmt)
      | _ => unloweredDoStmt
  -- #25 loop lowering: `for (const x of rhs)` / `for (let i = 0; i < B; i++)`.
  -- EscapeAnalysis admits only lowerable shapes into do-mode; anything else
  -- (`.notLowerable`, a non-array operand) falls to the loud marker as
  -- defence-in-depth against phase drift.
  | s@(.forOfStmt _ _ _ _ _) :: rest | s@(.forStmt _ _ _ _ _) :: rest =>
      match LoopShape.classifyLoop s with
      -- `for (const x of rhs) { … }` → `for x in rhs do …`. An ident RHS
      -- threads its element type onto `x` in the body env; an array-literal
      -- RHS leaves the env unchanged (element type unknown without
      -- inference — affects refinement projection only, not correctness).
      | .forOf x rhs rhsExpr body =>
          let bodyEnv? : Option EmitEnv :=
            match rhs with
            | .arrayLit _ => some env
            | .ident arrName =>
                (arrayElemTy? env arrName).map fun et =>
                  { env with bindingEnv := env.bindingEnv.insert x et }
          match bodyEnv? with
          | none => unloweredDoStmt
          | some env' =>
              .forDo x (emitExprEnv env rhsExpr)
                  (emitBodyDo env' info (blockStmts body))
                :: emitBodyDo env info rest
      -- `for (let i = 0; i < B; i++) { … }` → `for i in [0:B] do …`. The
      -- range binder is a `Nat` while TS `number` is `Float`, so the body is
      -- prefixed with `let i : Float := i.toFloat`, shadowing the Nat binder
      -- for all downstream uses. A `.inr` bound emits `arr.size` directly —
      -- range bounds are Nat, so no Float coercion as in expression position.
      | .canonicalFor i bound body =>
          let iter? : Option LExpr :=
            match bound with
            | .inl n => some (.rangeTo (.int (Int.ofNat n)))
            | .inr arrName =>
                if (arrayElemTy? env arrName).isSome then
                  some (.rangeTo (.proj (.var arrName) "size"))
                else none
          match iter? with
          | none => unloweredDoStmt
          | some iterExpr =>
              let shim : LDoStmt :=
                .letPure i (some (.const "Float")) (.proj (.var i) "toFloat")
              let env' : EmitEnv :=
                { env with bindingEnv := env.bindingEnv.insert i .number }
              .forDo i iterExpr (shim :: emitBodyDo env' info (blockStmts body))
                :: emitBodyDo env info rest
      -- A non-canonical `for` desugars to `init; while (test) { body;
      -- update }` and re-enters this function, reusing the while lowering.
      | .notLowerable =>
          match LoopShape.desugarGeneralFor s with
          | some desugared => emitBodyDo env info (desugared ++ rest)
          | none => unloweredDoStmt
  -- `while (c) body` → `while c do …`; `do body while (c)` →
  -- `repeat … until !(c)`: TS loops WHILE the test holds, Lean's `repeat`
  -- runs UNTIL it does. The shape re-checks are defence-in-depth, as above.
  | .whileStmt _ test body :: rest =>
      if LoopShape.hasLabeledBreakOrContinue body then unloweredDoStmt
      else
        .whileDo (emitExprEnv env test) (emitBodyDo env info (blockStmts body))
          :: emitBodyDo env info rest
  | .doWhileStmt _ body test :: rest =>
      if LoopShape.hasLabeledBreakOrContinue body
          || LoopShape.hasOwnUnlabeledContinue body then unloweredDoStmt
      else
        match emitExprEnv env test with
        -- `do { B } while (true)` is equivalent to `while (true) { B }` — the
        -- guard is constant, so running the body before the first check makes
        -- no difference. Lower to `while true do …` rather than `repeat …
        -- until`, because a returns-on-every-path loop needs a trailing
        -- `unreachable!` tail (issue #64) and `repeat … until` must be the last
        -- element of a `do` sequence, so it cannot take that tail (issue #72).
        | .bool true =>
            .whileDo (.bool true) (emitBodyDo env info (blockStmts body))
              :: emitBodyDo env info rest
        | leanTest =>
            .repeatUntilDo (emitBodyDo env info (blockStmts body))
                (.app (.var "not") [leanTest])
              :: emitBodyDo env info rest
  -- #25: unlabeled break/continue map 1:1; trailing statements are dead code
  -- and dropped (same convention as `return`). Labeled forms fall through to
  -- the loud marker (EscapeAnalysis poisons them upstream).
  | .breakStmt _ none :: _ => [.breakDo]
  | .continueStmt _ none :: _ => [.continueDo]
  -- A list that ends without `return` is a branch falling through to the
  -- code after its `if` — emit nothing. The function-level trailing
  -- `return ()` (for void bodies) is appended by `emitFuncDecl`.
  | [] => []
  -- Genuinely effect-free statements.
  | .emptyStmt _ :: rest | .debuggerStmt _ :: rest => emitBodyDo env info rest
  -- Anything else reaching here is a SubsetCheck/emitter disagreement
  -- about do-mode lowerability — fail loudly (invalid Lean), never drop.
  | _ :: _ => unloweredDoStmt

/-- Declarator lowering inside do-mode: mutated names become `let mut`,
    everything else stays an immutable `let`. Mirrors `emitVarDecl`'s
    refinement-literal wrapping and bindingEnv threading. -/
partial def emitVarDeclDo (env : EmitEnv) (info : EscapeAnalysis.MutationInfo)
    (decls : List VariableDeclarator) (rest : List Statement) : List LDoStmt :=
  match decls with
  | [] => emitBodyDo env info rest
  | d :: moreDecls =>
      match d with
      | .mk _ (.identifier id) init typeAnnotation =>
          let ty := typeAnnotation.map emitType
          let targetTy : Option TSType := typeAnnotation
          let initExpr := match init with
            | some e => emitExprWithExpectedTy env targetTy e
            | none   => .var "()"
          let env' := recordDeclBinding env id.name typeAnnotation init
          let bind := if info.mutated.contains id.name
            then LDoStmt.letMut id.name ty initExpr
            else LDoStmt.letPure id.name ty initExpr
          bind :: emitVarDeclDo env' info moreDecls rest
      | _ => emitVarDeclDo env info moreDecls rest

end

/-- Lower a top-level `console.log(...)` call to its IO action, or `none`
    if `e` is not a `console.log` call. Single arg → `consoleLog e`;
    multi-arg → `consoleLogN [JSShow.jsShow e₁, …]`.

    NOTE: unlike the top-level `console.log` arm in `emit`, this does NOT
    special-case `@throws`-annotated callees. A call like
    `console.log(throwsFn(x))` inside an `if` branch would emit the raw
    `Except` value rather than matching on `.ok`/`.error`. This limitation
    is harmless at present because no in-scope or parked fixture exercises
    that combination; add a `@throws`-aware arm here if one does. -/
private def consoleLogAction (env : EmitEnv) : Expression → Option LExpr
  | .callExpr _
      (.memberExpr _ (.identifier _ "console") (.identifier _ "log") false _)
      args _ =>
      match args with
      | [arg] => some (.app (.var "consoleLog") [emitExprEnv env arg])
      | _ :: _ =>
          let argExprs := args.map (emitExprEnv env)
          let listLit := mkListLit (argExprs.map fun e => .app (.var "JSShow.jsShow") [e])
          some (.app (.var "consoleLogN") [listLit])
      | [] => some (.app (.var "pure") [.var "()"])
  | _ => none

/-- True when a top-level statement list contains at least one IO action
    (a `console.log` call or a nested `if`). Used to decide whether a tail
    needs `do`-sequencing after a preceding IO action. -/
private partial def stmtsHaveIO : List Statement → Bool
  | [] => false
  | s :: rest =>
      let hereIO : Bool := match s with
        | .ifStmt _ _ _ _ => true
        | .blockStmt _ inner => stmtsHaveIO inner
        | .exprStmt _ (.callExpr _
            (.memberExpr _ (.identifier _ "console") (.identifier _ "log") false _) _ _) => true
        | _ => false
      hereIO || stmtsHaveIO rest

/-- Top-level `console.log(arg)` as a do-element (#49). A faithful port of
    `buildModule`'s `console.log` arm: a single argument that is a `@throws`
    call matches on its `Except`; a single plain argument is `consoleLog arg`;
    multiple arguments lower to `consoleLogN [JSShow.jsShow …]`. Returns `none`
    if `e` is not a `console.log` call (or has no arguments). -/
private def consoleLogDoStmt (env : EmitEnv) (e : Expression) : Option LDoStmt :=
  match e with
  | .callExpr _
      (.memberExpr _ (.identifier _ "console") (.identifier _ "log") false _)
      args _ =>
      match args with
      | [arg] =>
          let calleeNameOpt : Option String := match arg with
            | .callExpr _ (.identifier _ fname) _ _ => env.funcThrowsEnv.get? fname |>.map (fun _ => fname)
            | _ => none
          let argExpr := emitExprEnv env arg
          match calleeNameOpt with
          | some _ =>
              let okArm : LPattern × List LDoStmt :=
                (.ctor "ok" [.var "v__"], [.doExpr (.app (.var "consoleLog") [.var "v__"])])
              let errArm : LPattern × List LDoStmt :=
                (.ctor "error" [.wildcard], [.doExpr (.app (.var "pure") [.var "()"])])
              some (.matchDo argExpr [okArm, errArm])
          | none => some (.doExpr (.app (.var "consoleLog") [argExpr]))
      | _ :: _ =>
          let argExprs := args.map (emitExprEnv env)
          let listLit := mkListLit (argExprs.map fun e => .app (.var "JSShow.jsShow") [e])
          some (.doExpr (.app (.var "consoleLogN") [listLit]))
      | [] => none
  | _ => none

/-- Bare top-level call as a do-element (#49). A faithful port of
    `buildModule`'s bare-call arm: the throwing-prelude constructors run their
    `*Effect`; `@throws` callees match on the `Except` (panicking on `.error`);
    plain calls are evaluated for side effects. `none` if `e` is not an
    identifier-headed call. -/
private def bareCallDoStmt (env : EmitEnv) (e : Expression) : Option LDoStmt :=
  match e with
  | .callExpr _ (.identifier _ fname) callArgs _ =>
      let asEffectName : Option String := match fname with
        | "asInteger" => some "asIntegerEffect"
        | "asNatural" => some "asNaturalEffect"
        | "asByte" => some "asByteEffect"
        | "asBit" => some "asBitEffect"
        | _ => none
      match asEffectName with
      | some effFn => some (.doExpr (.app (.var effFn) (callArgs.map (emitExprEnv env))))
      | none =>
        match env.funcThrowsEnv.get? fname with
        | some _ =>
            let callLExpr := emitExprEnv env e
            let okArm : LPattern × List LDoStmt :=
              (.ctor "ok" [.wildcard], [.doExpr (.app (.var "pure") [.var "()"])])
            let errArm : LPattern × List LDoStmt :=
              (.ctor "error" [.wildcard], [.doExpr (.app (.var "panic!") [.str s!"throw from {fname}"])])
            some (.matchDo callLExpr [okArm, errArm])
        | none => some (.doExpr (emitExprEnv env e))
  | _ => none

/-- Top-level `try { console.log(f(args)) } catch (e) { console.log(g) }` where
    `f` is `@throws`, as a do-element (#49). A faithful port of `buildModule`'s
    try/catch arm: a `match` on the `Except`, with the catch body's
    `console.log` as the `.error` action. `none` if no such shape. -/
private def tryCatchDoStmt (env : EmitEnv) : Statement → Option LDoStmt
  | .tryStmt _ tryBlock (some (CatchClause.mk _ paramOpt catchBody _catchType)) _finalizer =>
      let tryStmts := match tryBlock with
        | .blockStmt _ stmts => stmts
        | other => [other]
      let catchVar : String := match paramOpt with
        | some (.identifier id) => id.name
        | _ => "e__"
      let catchStmts := match catchBody with
        | .blockStmt _ stmts => stmts
        | other => [other]
      let catchEffect : Option LExpr := catchStmts.findSome? fun s =>
        match s with
        | .exprStmt _ (.callExpr _
            (.memberExpr _ (.identifier _ "console") (.identifier _ "log") false _)
            [catchArg] _) =>
            some (.app (.var "consoleLog") [emitExprEnv env catchArg])
        | _ => none
      tryStmts.findSome? fun s =>
        match s with
        | .exprStmt _ (.callExpr _
            (.memberExpr _ (.identifier _ "console") (.identifier _ "log") false _)
            [(.callExpr _ (.identifier _ calleeName) _ _)] _) =>
            match env.funcThrowsEnv.get? calleeName with
            | some _ =>
                let callLExpr := match s with
                  | .exprStmt _ (.callExpr _ _ [cArg] _) => emitExprEnv env cArg
                  | _ => .var "()"
                let okArm : LPattern × List LDoStmt :=
                  (.ctor "ok" [.var "v__"], [.doExpr (.app (.var "consoleLog") [.var "v__"])])
                let errArm : LPattern × List LDoStmt :=
                  (.ctor "error" [.var catchVar],
                   [.doExpr (catchEffect.getD (.app (.var "pure") [.var "()"]))])
                some (.matchDo callLExpr [okArm, errArm])
            | none => none
        | _ => none
  | _ => none

mutual

/-- IO-aware sibling of `emitBodyEnv`: lower a top-level statement list into a
    single `LExpr : IO Unit`. Unlike `emitBodyEnv` (which is pure and *drops*
    `console.log`), this preserves `console.log` as a `consoleLog`/`consoleLogN`
    IO action and sequences multiple actions with a `do` block. `const`
    declarations become let-in bindings wrapping the IO continuation;
    refinement-narrowing `if`s reuse the `dite` machinery from `emitBodyEnv`. -/
partial def emitIOBodyEnv (env : EmitEnv) : List Statement → LExpr
  | [] => .app (.var "pure") [.var "()"]
  | .variableDecl (.mk _ decls _) :: rest =>
      emitVarDecl env decls (fun env' => emitIOBodyEnv env' rest)
  | .ifStmt _ cond thn elsOpt :: rest =>
      emitIfIO env cond thn elsOpt rest
  | .blockStmt _ inner :: rest => emitIOBodyEnv env (inner ++ rest)
  | (.exprStmt _ e) :: rest =>
      match consoleLogAction env e with
      | some act =>
          if stmtsHaveIO rest then .doSeq [act, emitIOBodyEnv env rest]
          else act
      | none => emitIOBodyEnv env rest
  | _ :: rest => emitIOBodyEnv env rest

/-- Lower a top-level `if (cond) thn else? elsOpt` followed by `rest` into an
    IO action. The `if` itself is self-contained (its narrowing does not
    extend into `rest`); `rest` is sequenced afterwards via `do` when it
    carries IO. The refinement-narrowing case reuses the exact `dite` shape
    from `emitBodyEnv`: `if h : pred x = true then let x : T := ⟨x, h⟩; … else …`. -/
partial def emitIfIO (env : EmitEnv) (cond : Expression) (thn : Statement)
    (elsOpt : Option Statement) (rest : List Statement) : LExpr :=
  let thnStmts : List Statement := match thn with
    | .blockStmt _ stmts => stmts
    | other => [other]
  let elseStmts : List Statement := match elsOpt with
    | some (.blockStmt _ stmts) => stmts
    | some other => [other]
    | none => []
  let elseExpr : LExpr := emitIOBodyEnv env elseStmts
  let ifAct : LExpr :=
    match detectRefinementPredicate cond with
    | some (varName, kind) =>
        let hName := s!"h{env.diteBinderCounter}"
        let predName := refinementKindPredicate kind
        let condExpr : LExpr :=
          .binOp "=" (.app (.var predName) [.var varName]) (.bool true)
        let env' : EmitEnv :=
          { env with
              bindingEnv := env.bindingEnv.insert varName (.refinement kind),
              diteBinderCounter := env.diteBinderCounter + 1 }
        let inner := emitIOBodyEnv env' thnStmts
        let shadowed : LExpr :=
          .letE varName (some (.const kind.name))
            (.anonCtor [.var varName] hName) inner
        .dite_ hName condExpr shadowed elseExpr
    | none =>
        .ite (emitExprEnv env cond) (emitIOBodyEnv env thnStmts) elseExpr
  if stmtsHaveIO rest then .doSeq [ifAct, emitIOBodyEnv env rest]
  else ifAct

end

mutual

/-- Lower a top-level statement list into the statements of `def main : IO Unit
    := do …` (#49). The single host for all executable module-level code.
    Mirrors `emitBodyDo` (the `Id.run do` emitter for function bodies) but:
    (a) targets a plain IO `do`, so it keeps `console.log` and bare calls
    instead of dropping them; (b) has no `return` value; (c) handles top-level
    `try`/`catch`. The mutation/loop arms are verbatim ports of `emitBodyDo`'s
    with the recursion retargeted to `emitIOBodyDo`. -/
partial def emitIOBodyDo (env : EmitEnv) (info : EscapeAnalysis.MutationInfo)
    : List Statement → List LDoStmt
  | [] => []
  | .variableDecl (.mk _ decls _) :: rest =>
      emitIOVarDeclDo env info decls rest
  -- `x = e` / `x OP= e`
  | .exprStmt _ (.assignmentExpr b op (.identifier _ name) rhs) :: rest =>
      let value : LExpr :=
        match op.compoundToBinary with
        | some binOp => emitExprEnv env (.binaryExpr b binOp (.identifier b name) rhs)
        | none => emitExprEnv env rhs
      .assign name value :: emitIOBodyDo env info rest
  -- `x++` / `x--`
  | .exprStmt _ (.updateExpr b op (.identifier _ name) _) :: rest =>
      let one : Expression := .literal b (.number 1) "1"
      let binOp : BinaryOperator := match op with | .inc => .add | .dec => .sub
      .assign name (emitExprEnv env (.binaryExpr b binOp (.identifier b name) one))
        :: emitIOBodyDo env info rest
  | .blockStmt _ inner :: rest => emitIOBodyDo env info (inner ++ rest)
  -- top-level try/catch (port of buildModule's `#eval match` arm)
  | (s@(.tryStmt _ _ _ _)) :: rest =>
      match tryCatchDoStmt env s with
      | some stmt => stmt :: emitIOBodyDo env info rest
      | none => emitIOBodyDo env info rest
  -- `if`: a plain boolean condition threads mutation via `ifDo`; a narrowing
  -- condition (refinement predicate or null-test) reuses `emitIfIO` embedded
  -- as a bare IO action (parity path — preserves the `dite` narrowing).
  | .ifStmt _ cond thn elsOpt :: rest =>
      match detectRefinementPredicate cond, nullCheckVar cond with
      | none, none =>
          let thnDo := emitIOBodyDo env info (blockStmts thn)
          let elsDo := match elsOpt with
            | some els => emitIOBodyDo env info (blockStmts els)
            | none => []
          .ifDo (emitExprEnv env cond) thnDo elsDo :: emitIOBodyDo env info rest
      | _, _ =>
          .doExpr (emitIfIO env cond thn elsOpt []) :: emitIOBodyDo env info rest
  -- console.log / bare calls / other expr statements (KEPT, unlike emitBodyDo)
  | .exprStmt _ e :: rest =>
      match consoleLogDoStmt env e with
      | some s => s :: emitIOBodyDo env info rest
      | none =>
        match bareCallDoStmt env e with
        | some s => s :: emitIOBodyDo env info rest
        | none => emitIOBodyDo env info rest   -- effect-free expr: drop
  -- #25 loops — verbatim ports of emitBodyDo arms with emitIOBodyDo recursion
  | s@(.forOfStmt _ _ _ _ _) :: rest | s@(.forStmt _ _ _ _ _) :: rest =>
      match LoopShape.classifyLoop s with
      | .forOf x rhs rhsExpr body =>
          let bodyEnv? : Option EmitEnv :=
            match rhs with
            | .arrayLit _ => some env
            | .ident arrName =>
                (arrayElemTy? env arrName).map fun et =>
                  { env with bindingEnv := env.bindingEnv.insert x et }
          match bodyEnv? with
          | none => unloweredDoStmt
          | some env' =>
              .forDo x (emitExprEnv env rhsExpr) (emitIOBodyDo env' info (blockStmts body))
                :: emitIOBodyDo env info rest
      | .canonicalFor i bound body =>
          let iter? : Option LExpr :=
            match bound with
            | .inl n => some (.rangeTo (.int (Int.ofNat n)))
            | .inr arrName =>
                if (arrayElemTy? env arrName).isSome then
                  some (.rangeTo (.proj (.var arrName) "size")) else none
          match iter? with
          | none => unloweredDoStmt
          | some iterExpr =>
              let shim : LDoStmt := .letPure i (some (.const "Float")) (.proj (.var i) "toFloat")
              let env' : EmitEnv := { env with bindingEnv := env.bindingEnv.insert i .number }
              .forDo i iterExpr (shim :: emitIOBodyDo env' info (blockStmts body))
                :: emitIOBodyDo env info rest
      | .notLowerable =>
          match LoopShape.desugarGeneralFor s with
          | some desugared => emitIOBodyDo env info (desugared ++ rest)
          | none => unloweredDoStmt
  | .whileStmt _ test body :: rest =>
      if LoopShape.hasLabeledBreakOrContinue body then unloweredDoStmt
      else .whileDo (emitExprEnv env test) (emitIOBodyDo env info (blockStmts body))
        :: emitIOBodyDo env info rest
  | .doWhileStmt _ body test :: rest =>
      if LoopShape.hasLabeledBreakOrContinue body
          || LoopShape.hasOwnUnlabeledContinue body then unloweredDoStmt
      else
        match emitExprEnv env test with
        | .bool true => .whileDo (.bool true) (emitIOBodyDo env info (blockStmts body))
            :: emitIOBodyDo env info rest
        | leanTest => .repeatUntilDo (emitIOBodyDo env info (blockStmts body))
            (.app (.var "not") [leanTest]) :: emitIOBodyDo env info rest
  | .breakStmt _ none :: _ => [.breakDo]
  | .continueStmt _ none :: _ => [.continueDo]
  | .emptyStmt _ :: rest | .debuggerStmt _ :: rest => emitIOBodyDo env info rest
  | _ :: _ => unloweredDoStmt

/-- Top-level declarator lowering (#49): mutated names become `let mut`,
    everything else an immutable `let`. Mirrors `emitVarDeclDo`. -/
partial def emitIOVarDeclDo (env : EmitEnv) (info : EscapeAnalysis.MutationInfo)
    (decls : List VariableDeclarator) (rest : List Statement) : List LDoStmt :=
  match decls with
  | [] => emitIOBodyDo env info rest
  | .mk _ (.identifier id) init typeAnnotation :: moreDecls =>
      let ty := typeAnnotation.map emitType
      let initExpr := match init with
        | some e => emitExprWithExpectedTy env typeAnnotation e
        | none   => .var "()"
      let env' := recordDeclBinding env id.name typeAnnotation init
      let bind := if info.mutated.contains id.name
        then LDoStmt.letMut id.name ty initExpr
        else LDoStmt.letPure id.name ty initExpr
      bind :: emitIOVarDeclDo env' info moreDecls rest
  | _ :: moreDecls => emitIOVarDeclDo env info moreDecls rest

end

/-- Emit a TypeScript function declaration. `total = true` emits a `def`
    (forcing Lean's termination checker); otherwise `partial def`. -/
def emitFuncDecl (aliasEnv : Std.HashMap String TSType) (name : String) (typeParams : List String)
    (params : List (String × TSType)) (retTy : TSType)
    (body : Statement) (throws : List String := [])
    (funcThrowsEnv : Std.HashMap String (List String) := {})
    (funcParamTypes : Std.HashMap String (List TSType) := {})
    (total : Bool := false)
    (funcRetTypes : Std.HashMap String TSType := {})
    (topBindings : Std.HashMap String TSType := {})
    (structFields : Std.HashMap String (List (String × TSType)) := {})
    (thisName : Option String := none)
    (classCtorParams : Std.HashMap String (List (String × TSType)) := {})
    (importedNames : Std.HashSet String := {}) : Option LDecl :=
  let normalizedRetTy := normalizeForEmit retTy
  let normalizedParams := params.map fun (n, t) => (n, normalizeForEmit t)
  -- Seed with the top-level bindings, which `emit` passes pre-normalized
  -- (TH0032 forbids shadowing, so params and locals can't collide with
  -- them in accepted programs); params win.
  let bindingEnv : Std.HashMap String TSType :=
    normalizedParams.foldl (fun m (n, t) => m.insert n t) topBindings
  let env : EmitEnv := { aliasEnv, bindingEnv, retTy := some normalizedRetTy,
                         throwTypes := throws, funcThrowsEnv, funcParamTypes,
                         funcRetTypes, structFields, thisName, classCtorParams,
                         importedNames }
  let stmts := match body with
    | .blockStmt _ ss => ss
    | other           => [other]
  -- #24/#25: a body with an eligible statement-position mutation (#24) OR a
  -- lowerable loop (#25) lowers to `Id.run do`; everything else keeps the
  -- pure path untouched.  `@throws` functions never reach do-mode (TH0007
  -- upstream), and `doModeLowerable` is the same function-level gate
  -- SubsetCheck's mutation routing rejects on (#40/#41) — checked here too
  -- so a checker regression degrades to the pure path instead of a
  -- miscompile.  Loop-triggered entry is needed because the pure expression
  -- path has no host for a `for … in … do` statement (#25).
  let info := EscapeAnalysis.analyze (params.map (·.1)) body
  let hasEligibleMutation := info.mutated.toList.any info.eligible
  let bodyExpr :=
    if (hasEligibleMutation || info.hasLowerableLoop) && info.doModeLowerable && throws.isEmpty then
      -- Mutated parameters self-shadow as `let mut x := x`: JS parameters
      -- are mutable locals whose mutation never affects the caller.
      let prologue : List LDoStmt := normalizedParams.filterMap fun (n, _) =>
        if info.mutated.contains n && info.eligible n
        then some (.letMut n none (.var n))
        else none
      let core := prologue ++ emitBodyDo env info stmts
      -- A body that can fall off the end (void function) needs an explicit
      -- unit return; appending one after an always-returning body would be
      -- dead code at the wrong type.
      let core := finalizeDoBody core
      .idRunDo core
    else
      emitBodyEnv env stmts
  let leanParams := normalizedParams.map fun (n, t) => (n, emitType t)
  let leanRetTy :=
    if throws.isEmpty then emitType normalizedRetTy
    else buildExceptRetTy throws (emitType normalizedRetTy)
  some (.def_ name typeParams leanParams leanRetTy bodyExpr (isPartial := !total))

/-- Lower a v1 class declaration (#106) to `structure C where <fields>` plus
    `namespace C` holding `def ctor'` and receiver-first `partial def`s.
    The ctor's `this.<f> = <e>` assignments become `let f := ⟦e⟧` in source
    order (ctor mode maps `this.<g>` reads to the already-bound `let g`);
    the final expression is the struct literal over all fields. Methods reuse
    the `emitFuncDecl` body pipeline with a leading `self' : C` receiver.
    Assumes the subset check passed; malformed members are skipped. -/
def emitClassDecl (env : EmitEnv) (topBindings : Std.HashMap String TSType)
    (className : String) (body : List ClassElement) : List LDecl :=
  let fields : List (String × TSType) := body.filterMap fun
    | .field (.mk _ key _ false false none _ _ ann _) =>
        match key with
        | .identifier _ n => some (n, ann.getD .any)
        | _ => none
    | _ => none
  let structDecl : LDecl :=
    .struct className [] (fields.map fun (n, t) => (n, emitType (normalizeForEmit t)))
  let ctorMember? : Option MethodDefinition := body.findSome? fun
    | .method (md@(.mk _ _ _ .constructor ..)) => some md
    | _ => none
  let ctorParams : List (String × TSType) := match ctorMember? with
    | some (.mk _ _ _ _ _ _ _ _ _ _ _ sigParams _) =>
        sigParams.map fun (n, ann, _, _) => (n, (ann.map (·.type)).getD .any)
    | none => []
  let assignments : List (String × Expression) := match ctorMember? with
    | some (.mk _ _ (.functionExpr _ _ _ cbody _ _) ..) =>
        let stmts : List Statement := match cbody with
          | .blockStmt _ ss => ss
          | s => [s]
        stmts.filterMap fun
          | .exprStmt _ (.assignmentExpr _ .assign
              (.memberExpr _ (.thisExpr _) (.identifier _ f) false _) rhs) => some (f, rhs)
          | _ => none
    | _ => []
  let ctorEnv : EmitEnv := { env with
    bindingEnv := ctorParams.foldl (fun m (n, t) => m.insert n (normalizeForEmit t)) topBindings,
    ctorMode := true, thisName := none, retTy := some (.ref className []) }
  let fieldTy (f : String) : Option TSType := (fields.lookup f).map normalizeForEmit
  let ctorBody : LExpr := assignments.foldr
    (fun (f, rhs) acc => .letE f none (emitExprWithExpectedTy ctorEnv (fieldTy f) rhs) acc)
    (.structLit className (fields.map fun (f, _) => (f, .var f)))
  let ctorDef : LDecl := .def_ "ctor'" []
    (ctorParams.map fun (n, t) => (n, emitType (normalizeForEmit t)))
    (.const className) ctorBody (isPartial := false)
  let methodDefs : List LDecl := body.filterMap fun
    | .method (.mk _ key value .method false false none _ _ _ _ sigParams returnType) =>
        match key, value with
        | .identifier _ mname, .functionExpr _ _ _ mbody _ _ =>
            let params := ("self'", TSType.ref className [])
              :: sigParams.map fun (n, ann, _, _) => (n, (ann.map (·.type)).getD .any)
            let retTy := (returnType.map (·.type)).getD .any
            emitFuncDecl env.aliasEnv mname [] params retTy mbody []
              env.funcThrowsEnv env.funcParamTypes false env.funcRetTypes topBindings
              env.structFields (thisName := some "self'")
              (classCtorParams := env.classCtorParams) (importedNames := env.importedNames)
        | _, _ => none
    | _ => none
  [structDecl, .namespace_ className (ctorDef :: methodDefs)]

private def arrowFuncParts (arrowParams : List FunctionParam) (typeAnn : Option TypeAnnotation)
    : List (String × TSType) × TSType :=
  -- Extract param names from the AST (types are not stored in FunctionParam for arrow exprs)
  let names : List String := arrowParams.filterMap fun
    | .simple id      => some id.name
    | .withDefault id _ => some id.name
    | .rest id        => some id.name
    | .pattern _      => none
  match typeAnn with
  | some ann =>
      match ann.type with
      | .function ps ret =>
          let paired := names.zipWith (fun n (p : TSParamType) =>
            match p with | .mk _ t _ _ => (n, t)) ps
          let remaining := names.drop ps.length |>.map (·, TSType.any)
          (paired ++ remaining, ret)
      | other =>
          -- Annotation is the return type directly: `const f: number = () => ...`.
          (names.map (·, TSType.any), other)
  | none =>
      (names.map (·, TSType.any), .any)

/-- Convert a module specifier path to a Lean module name:
    `"./utils/arr"` → `"Utils.Arr"`. -/
private def pathToLeanModule (path : String) : String :=
  let parts := path.splitOn "/"
  let cleaned := parts.filterMap fun p =>
    if p.isEmpty || p = "." || p = ".." then none
    else
      let alnum := p.toList.filter fun c => c.isAlphanum
      match alnum with
      | [] => none
      | c :: rest => some (String.ofList (c.toUpper :: rest))
  String.intercalate "." cleaned

/-- Translate relative TS imports into Lean module names; bare specifiers are skipped. -/
private def collectImports (body : List TSStatement) : List String :=
  body.filterMap fun
    | .importDecl _ source _ _ _ =>
        if source.startsWith "./" || source.startsWith "../" then
          let m := pathToLeanModule source
          if m.isEmpty then none else some m
        else none
    | _ => none

/-- Produce selective `open` clauses per relative named import, so imported
    names are usable unqualified. Specifiers split by whether they alias:
    `import { inc, makeFoo as build } from './a'` →
    `A (inc)` and `A renaming makeFoo → build`, rendered as two `open` lines.
    A single combined `open` cannot mix plain and renaming, so they stay separate. -/
private def collectOpens (body : List TSStatement) : List String :=
  body.flatMap fun
    | .importDecl _ source specs .named _ =>
        if (source.startsWith "./" || source.startsWith "../") && !specs.isEmpty then
          let m := pathToLeanModule source
          if m.isEmpty then []
          else
            let plain := specs.filter fun sp => sp.imported == sp.localName
            let renamed := specs.filter fun sp => sp.imported != sp.localName
            let plainOpen : List String :=
              if plain.isEmpty then []
              else [s!"{m} ({String.intercalate " " (plain.map (·.imported))})"]
            let renameOpen : List String :=
              if renamed.isEmpty then []
              else
                let pairs := renamed.map fun sp => s!"{sp.imported} → {sp.localName}"
                [s!"{m} renaming {String.intercalate ", " pairs}"]
            plainOpen ++ renameOpen
        else []
    | _ => []

/-- Build a map from function name → throws list from annotated function declarations. -/
private def buildFuncThrowsEnv (body : List TSStatement) : Std.HashMap String (List String) :=
  body.foldl (fun env ts =>
    match ts with
    | .annotatedFuncDecl _ name _ _ _ _ _ _ throwsAnn _ =>
        match throwsAnn with
        | .declared (t :: ts') => env.insert name (t :: ts')
        | .declared [] | .absent => env
    | _ => env) {}

/-- Build a map from function name → declared parameter types. Used at call
    sites to coerce numeric literal args into refinement-typed slots
    (e.g. `safeAt(xs, 1 as Natural)` — after the parser strips the cast,
    the arg is just `1`; here we re-attach the target type so the emit
    wraps it in a Subtype constructor). -/
private def buildFuncParamTypesEnv (body : List TSStatement) : Std.HashMap String (List TSType) :=
  body.foldl (fun env ts =>
    match ts with
    | .annotatedFuncDecl _ name _ params _ _ _ _ _ _ =>
        let paramTys := params.map fun (_, annot, _, _) =>
          match annot with | some a => a.type | none => TSType.any
        env.insert name paramTys
    | _ => env) {}

/-- Build a map from function name → declared return type (normalized for
    emission, so `T | undefined` arrives as `.option T`). Feeds the
    initializer-shape inference for un-annotated `const x = f(...)`. -/
private def buildFuncRetTypesEnv (body : List TSStatement) : Std.HashMap String TSType :=
  body.foldl (fun env ts =>
    match ts with
    | .annotatedFuncDecl _ name _ _ (some retAnn) _ _ _ _ _ =>
        env.insert name (normalizeForEmit retAnn.type)
    | _ => env) {}

/-- Build a `TypeContext` for the emit pass: registers each top-level type
    alias and the declared type of each annotated `const`/`let`/`var`. Used
    to resolve type-level constructs like `__typeof X` and `__indexAccess`. -/
private def buildEmitTypeContext (body : List TSStatement) : TypeContext :=
  let aliases : Std.HashMap String TypeAliasDef := body.foldl (fun env ts =>
    match ts with
    | .typeAliasDecl _ name tps ty =>
        env.insert name { typeParams := tps, body := ty }
    | _ => env) {}
  let bindings : Std.HashMap String TSType := body.foldl (fun env ts =>
    match ts with
    | .annotatedVarDecl _ _ name (some typeAnn) _ =>
        env.insert name typeAnn.type
    | _ => env) {}
  { bindings, typeAliases := aliases }

/-- Pre-resolve every top-level type alias body. Markers like `__typeof X`
    and `__indexAccess[arr, number]` collapse to their concrete result so
    the emitter sees plain Lean-renderable types. -/
private def resolveAliases (body : List TSStatement) : Std.HashMap String TSType :=
  let ctx := buildEmitTypeContext body
  body.foldl (fun env ts =>
    match ts with
    | .typeAliasDecl _ name _ ty =>
        let resolved := runTypeCheckMValue ctx (resolveTypeGeneric ty)
        env.insert name resolved
    | _ => env) {}

/-- The declared name of a top-level statement, for export/privacy bookkeeping. -/
private def declName : TSStatement → Option String
  | .annotatedFuncDecl _ n .. => some n
  | .annotatedVarDecl _ _ n .. => some n
  | .interfaceDecl _ n .. => some n
  | .typeAliasDecl _ n .. => some n
  | .enumDecl _ n .. => some n
  | .js (.classDecl _ id ..) => some id.name
  | _ => none

/-- The name an emitted decl binds, for privacy marking (`eval_`/`instance_` bind none). -/
private def ldeclName : LDecl → Option String
  | .def_ n .. => some n
  | .struct n .. => some n
  | .inductive_ n .. => some n
  | .abbrev_ n .. => some n
  | _ => none

/-- The JS statement a top-level item contributes to `def main`, or `none` if
    it is a hoisted declaration (function / type / interface / enum, a `const`,
    or a non-mutated `let` — all emitted as top-level `def`s). A `let` mutated
    somewhere at module level (`mutatedTop`) is reconstructed as a
    `.variableDecl` so `emitIOVarDeclDo` lowers it to a `let mut` inside `main`
    (#49). -/
private def mainStreamStmt (mutatedTop : Std.HashSet String) : TSStatement → Option Statement
  | .js (.variableDecl _) => none  -- top-level var decls arrive as annotatedVarDecl
  | .js s =>
      match s with
      | .exprStmt _ _ | .ifStmt _ _ _ _ | .tryStmt _ _ _ _
      | .forOfStmt _ _ _ _ _ | .forStmt _ _ _ _ _
      | .whileStmt _ _ _ | .doWhileStmt _ _ _ | .blockStmt _ _ => some s
      | _ => none
  | .annotatedVarDecl b _kind name typeAnn (some init) =>
      if mutatedTop.contains name then
        some (.variableDecl (.mk b [.mk b (.identifier { name }) (some init) (typeAnn.map (·.type))] .let_))
      else none
  | _ => none

/-- Walk the program and produce a Lean module (structural form). -/
def buildModule (prog : TSProgram) (moduleName : String) : LModule :=
  let resolvedAliases := resolveAliases prog.body
  let funcThrowsEnv := buildFuncThrowsEnv prog.body
  let funcParamTypes := buildFuncParamTypesEnv prog.body
  let funcRetTypes := buildFuncRetTypesEnv prog.body
  let tsImports := collectImports prog.body
  -- Top-level binding env: every `annotatedVarDecl` with a declared type
  -- contributes a binding so that `console.log(a + b)` can detect refinement
  -- operands and project `.val` accordingly.
  let topBindingEnv : Std.HashMap String TSType := prog.body.foldl (fun acc ts =>
    match ts with
    | .annotatedVarDecl _ _ name (some typeAnn) _ => acc.insert name typeAnn.type
    | .annotatedVarDecl _ _ name none (some (.arrayExpr _ elems)) =>
        -- A homogeneous numeric/string literal infers number[]/string[] (so the
        -- array-method override can lower it, #70); otherwise the conservative
        -- tuple-of-any placeholder.
        acc.insert name
          ((arrayLiteralType? elems).getD (.tuple (List.replicate elems.length .any)))
    | .annotatedVarDecl _ _ name none (some (.literal _ (.string _) _)) =>
        acc.insert name .string
    | .annotatedVarDecl _ _ name none (some (.callExpr _ (.identifier _ f) _ _)) =>
        match funcRetTypes.get? f with
        | some t => acc.insert name t
        | none => acc
    | .annotatedVarDecl _ _ name none (some (.newExpr _ (.identifier _ c) _)) =>
        -- `const s = new C(...)`: record the class instance type so
        -- name-keyed member reads (e.g. a `length` field) resolve (#106)
        acc.insert name (.ref c [])
    | _ => acc) {}
  -- Map every interface and single-record `type` alias to its declared fields
  -- (in order), so object-literal construction can resolve the target structure
  -- and field types (#15/#81). Unwrap `export <decl>` so `export interface` /
  -- `export type` are registered too.
  let structFields : Std.HashMap String (List (String × TSType)) :=
    (prog.body.map fun s => match s with
      | .exportDecl _ inner => inner
      | other => other).foldl (fun acc ts =>
      match ts with
      | .interfaceDecl _ name _ _ members =>
          acc.insert name (interfaceFields members)
      | .typeAliasDecl _ name _ _ =>
          match resolvedAliases[name]? with
          | some (.object members) =>
              acc.insert name (objectTypeFields members)
          | _ => acc
      -- Class fields register like interface fields so structural
      -- construction (`const q: Point = { x, y }`) resolves (#106)
      | .js (.classDecl _ id _ cbody ..) =>
          acc.insert id.name (cbody.filterMap fun
            | .field (.mk _ (.identifier _ n) _ false false none _ _ ann _) =>
                some (n, ann.getD .any)
            | _ => none)
      | _ => acc) {}
  -- Class registry: ctor param types per local class, for `new C(args)` (#106)
  let classCtorParams : Std.HashMap String (List (String × TSType)) :=
    (prog.body.map fun s => match s with
      | .exportDecl _ inner => inner
      | other => other).foldl (fun acc ts =>
      match ts with
      | .js (.classDecl _ id _ cbody ..) =>
          let ps : List (String × TSType) := cbody.findSome? (fun el => match el with
            | .method (.mk _ _ _ .constructor _ _ _ _ _ _ _ sigParams _) =>
                some (sigParams.map fun (n, ann, _, _) => (n, (ann.map (·.type)).getD TSType.any))
            | _ => none) |>.getD []
          acc.insert id.name ps
      | _ => acc) {}
  -- Value names bound by import specifiers (for `new <imported>(…)`)
  let importedNames : Std.HashSet String := prog.body.foldl (fun acc ts =>
    match ts with
    | .importDecl _ _ specs _ _ => specs.foldl (fun a sp => a.insert sp.localName) acc
    | _ => acc) {}
  let topEnv : EmitEnv := { aliasEnv := resolvedAliases, bindingEnv := topBindingEnv,
                            funcThrowsEnv, funcParamTypes, funcRetTypes, structFields,
                            classCtorParams, importedNames }
  -- Normalized once here; every `emitFuncDecl` call seeds its bindingEnv
  -- from this map.
  let topBindingsNorm : Std.HashMap String TSType :=
    topBindingEnv.fold (fun m k v => m.insert k (normalizeForEmit v)) {}
  let optToList : Option LDecl → List LDecl := fun
    | some d => [d]
    | none => []
  -- Pair each top-level item with its index so that the dite-binder counter
  -- can be seeded distinctly per item (two top-level `if`s would otherwise
  -- both start at `h0` and collide). `16` leaves generous headroom for the
  -- number of `dite` binders any single top-level statement could introduce.
  -- Names that are publicly exported (inline `export <decl>` or trailing
  -- `export { … }`). When a module has any exports, every other top-level decl
  -- is emitted `private` so it cannot leak into an importer via `import A`.
  -- For trailing `export { local as public }`, the PUBLIC name (`localName`) is
  -- the export; the local decl (`imported`) stays private and gets a public
  -- alias `def public := local` (below). For `export { g }` the two coincide.
  let exportedNames : List String := prog.body.foldl (fun acc s => match s with
    | .exportDecl _ inner => acc ++ (declName inner).toList
    | .exportNamedDecl _ specs => acc ++ specs.map (·.localName)
    | _ => acc) []
  let hasExports : Bool := prog.body.any fun s => match s with
    | .exportDecl _ _ | .exportNamedDecl _ _ => true
    | _ => false
  -- Unwrap `export <decl>` to its inner declaration so the existing arms emit it
  -- unchanged; `exportNamedDecl`/`exportUnsupported` carry no decl (catch-all).
  let bodyForEmit : List TSStatement := prog.body.map fun s => match s with
    | .exportDecl _ inner => inner
    | other => other
  -- Module-level mutation/loop analysis over the executable top-level
  -- statements (var decls reconstructed so their bindings are seen), treated
  -- as one block (no params at module level). The SAME block the subset
  -- checker analyzes (#49). Drives the `let mut` vs hoisted-`def` split for
  -- top-level `let`s.
  let moduleStmts : List Statement := moduleExecutableStatements prog.body
  let moduleInfo : EscapeAnalysis.MutationInfo :=
    EscapeAnalysis.analyze [] (.blockStmt {} moduleStmts)
  let mutatedTop : Std.HashSet String := moduleInfo.mutated
  let decls : List LDecl := bodyForEmit.flatMap fun ts =>
    match ts with
    | .typeAliasDecl _ name tps ty =>
        let bodyTy := resolvedAliases.getD name ty
        emitTypeAlias name (typeParamNames tps) bodyTy
    | .interfaceDecl _ name tps _extends members =>
        [emitInterface name (typeParamNames tps) members]
    | .annotatedFuncDecl _ name tps params retAnnot body _gen _async throwsAnn total =>
        let simpleParams := params.map fun (n, annot, _opt, _rest) =>
          (n, match annot with | some a => a.type | none => .any)
        let retTy := match retAnnot with
          | some a => a.type
          | none => .any
        let throws : List String := match throwsAnn with
          | .declared ts => ts
          | .absent      => []
        optToList (emitFuncDecl resolvedAliases name (typeParamNames tps) simpleParams retTy body throws funcThrowsEnv funcParamTypes total funcRetTypes topBindingsNorm structFields none classCtorParams importedNames)
    | .annotatedVarDecl _ _kind name typeAnn (some init) =>
        if mutatedTop.contains name then []   -- mutated let → lowered inside `main`
        else
        match init with
        | .arrowFunctionExpr _ arrowParams body _isExpr async arrowRetAnn =>
            if async then []
            else
              -- Arrow's own return annotation wins; var-decl annotation is the fallback.
              let effectiveAnn := arrowRetAnn <|> typeAnn
              let (simpleParams, retTy) := arrowFuncParts arrowParams effectiveAnn
              optToList (emitFuncDecl resolvedAliases name [] simpleParams retTy (match body with
                | .inl e  => .blockStmt {} [.returnStmt {} (some e)]
                | .inr s  => s) [] funcThrowsEnv funcParamTypes false funcRetTypes topBindingsNorm structFields none classCtorParams importedNames)
        | other =>
            -- Non-arrow const: prefer the user's annotation when present.
            -- Otherwise, attempt to infer a Lean type from the initializer
            -- shape (e.g. `[10, 20, 30]` → `Array Float`). Without a usable
            -- type, the decl is silently skipped (the type-checker will have
            -- diagnosed the use-site already).
            match typeAnn with
            | some ann =>
                let initExpr := emitExprWithExpectedTy topEnv (some ann.type) other
                [.def_ name [] [] (emitType ann.type) initExpr]
            | none =>
                -- Unannotated `const x = init`: emit `def x := init` and
                -- let Lean infer the type. Skip when the initializer is
                -- something we don't yet know how to lower (a placeholder
                -- `(unsupported expr)` would not elaborate).
                let initExpr := emitExprEnv topEnv other
                [.def_ name [] [] .inferred initExpr]
    -- v1 class declarations lower to `structure` + `namespace` (#106)
    | .js (.classDecl _ id _ cbody ..) =>
        emitClassDecl topEnv topBindingsNorm id.name cbody
    -- Executable top-level statements (bare calls, `console.log`, `try`/`catch`,
    -- `if`, loops, mutation) are no longer emitted here as scattered `#eval`s;
    -- they flow into the single `def main` do-block below (#49).
    | _ => []
  -- For each trailing `export { local as public }` (local ≠ public), emit a
  -- public alias `def public := local`, appended after the originals so the
  -- referenced local decl is already in scope.
  let exportAliasDecls : List LDecl := prog.body.flatMap fun s => match s with
    | .exportNamedDecl _ specs =>
        specs.filterMap fun sp =>
          if sp.imported != sp.localName then
            some (.def_ sp.localName [] [] .inferred (.var sp.imported))
          else none
    | _ => []
  let decls : List LDecl := decls ++ exportAliasDecls
  -- Mark non-exported named decls `private` (only in modules that export).
  -- A class namespace cannot be marked wholesale (`private namespace` is not
  -- legal Lean); privacy distributes onto each decl inside it (#106).
  let decls : List LDecl :=
    if hasExports then
      decls.map fun d => match d with
        | .namespace_ n nbody =>
            if exportedNames.contains n then d
            else .namespace_ n (nbody.map (.private_ ·))
        | _ => match ldeclName d with
          | some n => if exportedNames.contains n then d else .private_ d
          | none => d
    else decls
  -- Collect executable top-level statements (source order) into `def main`,
  -- appended after the hoisted decls (so `main` can reference them) and after
  -- the `private`-marking pass (so `main` and its `#eval` stay public). A
  -- module with no executable statements is a pure library: no `main`, no
  -- `#eval` (#49).
  let mainStmts : List Statement := bodyForEmit.filterMap (mainStreamStmt mutatedTop)
  let mainDo : List LDoStmt := emitIOBodyDo topEnv moduleInfo mainStmts
  -- The entry point's name must not collide with a user `const main`/`function
  -- main` (a common idiom: `const main = () => …; console.log(main())`), so
  -- pick the first candidate that is not a top-level declared name.
  let topNames : Std.HashSet String := bodyForEmit.foldl (fun acc s =>
    match declName s with | some n => acc.insert n | none => acc) {}
  let entryName : String :=
    (["main", "_thalesMain", "_thalesEntry", "_thalesMain'"].find?
      (fun n => !topNames.contains n)).getD "_thalesMain"
  let decls : List LDecl :=
    if mainDo.isEmpty then decls
    else decls
      ++ [ .def_ entryName [] [] (.const "IO Unit") (.ioDo mainDo),
           .eval_ (.var entryName) ]
  let body : LDecl :=
    if moduleName.isEmpty then .namespace_ "Input" decls
    else .namespace_ moduleName decls
  {
    imports := "Thales.TS.Runtime" :: tsImports
    opens := "Thales.TS" :: collectOpens prog.body
    decls := [body]
  }

/-- Walk the program and produce a Lean module string. -/
def emit (prog : TSProgram) (moduleName : String) : String :=
  renderModule (buildModule prog moduleName)

end Thales.Emit
