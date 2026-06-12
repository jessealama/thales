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
  -- Counter used to generate unique dite-binder names. Bumped each time
  -- a fresh `h_i` is introduced (e.g. for `is<T>`-narrowing shadow-lets).
  diteBinderCounter : Nat := 0

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
  | _ => [.abbrev_ name typeParams (emitType ty)]

/-- Emit an interface as a Lean structure. Only property members are
    kept for v1; method members are skipped (v2 adds classes/methods). -/
def emitInterface (name : String) (typeParams : List String)
    (members : List TSInterfaceMember) : LDecl :=
  let fields := members.filterMap fun
    | .property fname fty _opt _ro => some (fname, emitType fty)
    | .method _ _ _ _ => none
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
    (`arr[k]?`, `Thales.TS.Array.get?`) already produce `Option T` and are
    passed through. Otherwise wrap in `.some`. -/
private def wrapReturn (retTy : Option TSType) (e : LExpr) : LExpr :=
  match retTy with
  | some (.option _) =>
    match e with
    | .ctor "none" [] => e
    | .var "undefined" => .ctor "none" []
    | .indexOpt _ _ => e
    | .app (.var "Thales.TS.Array.get?") _ => e
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
  [.ret (.var "(unsupported: statement not lowerable in do-mode)")]

/-- Unwrap a block into its statement list; a single statement becomes a
    singleton list. -/
private def blockStmts : Statement → List Statement
  | .blockStmt _ ss => ss
  | other => [other]

mutual

/-- Translate a JS `Expression` to a Lean `LExpr`. Unsupported constructs
    emit `.var "(unsupported expr)"`; SubsetCheck rejects them upstream.
    `env` carries the binding-type table so refinement-typed identifiers
    can be `.val`-projected when used in arithmetic. -/
partial def emitExprEnv (env : EmitEnv) : Expression → LExpr
  -- Literals
  | .literal _ (.number n) _ => .float n
  | .literal _ (.bigint n) _ => .int n
  | .literal _ (.string s) _ => .str s
  | .literal _ (.boolean b) _ => .bool b
  | .literal _ .null _       => .ctor "none" []
  | .literal _ (.regex _ _) _ => .var "(unsupported: regex literal)"
  -- Identifier
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
      .proj (.var varName) "isNone"
  -- `x !== null` / `x !== undefined` (and reverses, with `!=` too) → x.isSome
  | .binaryExpr _ .sneq (.identifier _ varName) (.literal _ .null _)
  | .binaryExpr _ .neq  (.identifier _ varName) (.literal _ .null _)
  | .binaryExpr _ .sneq (.literal _ .null _)    (.identifier _ varName)
  | .binaryExpr _ .neq  (.literal _ .null _)    (.identifier _ varName)
  | .binaryExpr _ .sneq (.identifier _ varName) (.identifier _ "undefined")
  | .binaryExpr _ .neq  (.identifier _ varName) (.identifier _ "undefined")
  | .binaryExpr _ .sneq (.identifier _ "undefined") (.identifier _ varName)
  | .binaryExpr _ .neq  (.identifier _ "undefined") (.identifier _ varName) =>
      .proj (.var varName) "isSome"
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
  | .unaryExpr _ _ _ _ => .var "(unsupported: unary op)"
  -- Update (++/--): SubsetCheck rejects; placeholder
  | .updateExpr _ _ _ _ => .var "(unsupported: update expr)"
  -- Conditional (ternary)
  | .conditionalExpr _ cond thn els =>
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
      let calleeFnName : Option String := match callee with
        | .identifier _ name => some name
        | _ => none
      let paramTys : List (Option TSType) := match calleeFnName with
        | some n => match env.funcParamTypes.get? n with
            | some tys => tys.map some ++ List.replicate (args.length - tys.length) none
            | none => List.replicate args.length none
        | none => List.replicate args.length none
      let coerceArg : Expression → Option TSType → LExpr := fun a tyOpt =>
        let raw := emitExprEnv env a
        match tyOpt with
        | some ty =>
            ((emitRefinementLiteral env.aliasEnv (some ty) a)
              <|> (emitLiteralAsCtor env.aliasEnv (some ty) a))
              |>.getD raw
        | none => raw
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
      | _ =>
          -- Unknown binding: best-effort `s.length.toFloat`.
          .proj (.proj (.var arrName) "length") "toFloat"
  | .memberExpr _ obj (.identifier _ propName) false _ =>
      .proj (emitExprEnv env obj) propName
  | .memberExpr _ obj idx true _ =>
      .app (.var "Thales.TS.Array.get?") [emitExprEnv env obj, emitExprEnv env idx]
  | .memberExpr _ obj _ _ _ =>
      .proj (emitExprEnv env obj) "(unknown)"
  -- Array expression: emit as List.toArray applied to nested cons/nil
  | .arrayExpr _ elements =>
      let exprs := elements.filterMap id |>.map (emitExprEnv env)
      .app (.var "List.toArray") [mkListLit exprs]
  -- Arrow function expression
  | .arrowFunctionExpr _ params body _ async _ =>
      if async then .var "(unsupported: async arrow)"
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
  -- Assignment: SubsetCheck rejects; placeholder
  | .assignmentExpr _ _ _ _ => .var "(unsupported: assignment)"
  -- Object literal with a `kind: "..."` discriminator: emit as an anonymous
  -- constructor `.kindVal <other-field-values>` and let Lean resolve which
  -- inductive via context. Field values are emitted in literal order, which
  -- must match the constructor's parameter order. For non-discriminated
  -- object literals there is no clean shallow embedding in v1 — fall through
  -- to the placeholder and rely on the type checker to have rejected earlier.
  | .objectExpr _ props =>
      let regularProps : List (String × Expression) := props.filterMap fun
        | .regular _ (.literal _ (.string k) _) v _ _ _ => some (k, v)
        | .regular _ (.identifier _ k) v _ _ _          => some (k, v)
        | _                                             => none
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
      | none => .var "(unsupported expr)"
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
  | _ => .var "(unsupported expr)"

/-- Backwards-compatible wrapper used by the few sites that have no env
    available (e.g. the top-level `console.log` lowering). Calls
    `emitExprEnv` with an empty env, which means refinement detection is
    skipped — the caller must guarantee operands are `Float`-typed. -/
partial def emitExpr : Expression → LExpr := emitExprEnv {}

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
            | some e =>
                ((emitRefinementLiteral env.aliasEnv targetTy e)
                  <|> (emitLiteralAsCtor env.aliasEnv targetTy e))
                  |>.getD (emitExprEnv env e)
            | none   => .var "()"
          let env' :=
            match typeAnnotation with
            | some t => { env with bindingEnv := env.bindingEnv.insert id.name t }
            | none   => env
          .letE id.name ty initExpr (emitVarDecl env' rest body)
      | _ => emitVarDecl env rest body  -- destructuring patterns skipped for v1

/-- Emit a list of statements as a Lean expression. Handles var decls, `if`,
    block, expression, `return`, and `switch` on discriminated unions. -/
partial def emitBodyEnv (env : EmitEnv) : List Statement → LExpr
  | .returnStmt _ (some e) :: _ =>
      let emitted :=
        ((emitRefinementLiteral env.aliasEnv env.retTy e)
          <|> (emitLiteralAsCtor env.aliasEnv env.retTy e))
          |>.getD (emitExprEnv env e)
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
            match env.bindingEnv.get? varName with
            | some (.option _) =>
                -- The THEN branch becomes its own match arm WITHOUT the
                -- continuation, so it must return on every path (the
                -- early-return idiom); otherwise control would fall out of
                -- the arm and the continuation — emitted only into the
                -- other arm — would be skipped. Non-returning branches keep
                -- the plain-ite fallback.
                if EscapeAnalysis.stmtsReturn [thn] then
                  let thnArm := emitBodyEnv env [thn]
                  -- Positive test (`x === null`): THEN is the none arm and
                  -- the continuation flows at the narrowed type via the
                  -- some-arm rebinding. Negated (`x !== null`, #43): the
                  -- arms swap — THEN gets the rebinding.
                  let arms :=
                    if positive then
                      [(LPattern.ctor "none" [], thnArm),
                       (LPattern.ctor "some" [.var varName], elseBody)]
                    else
                      [(LPattern.ctor "some" [.var varName], thnArm),
                       (LPattern.ctor "none" [], elseBody)]
                  .match_ (.var varName) arms
                else fallback
            | _ => fallback
        | none => fallback
  | .blockStmt _ inner :: rest => emitBodyEnv env (inner ++ rest)
  | .exprStmt _ _ :: rest      => emitBodyEnv env rest
  | .switchStmt _ discriminant cases :: _ =>
      -- SubsetCheck (TH0041) guarantees the discriminated `ident.field`
      -- shape with all-return arms, so the code after the switch is dead
      -- and a fallback that DROPS the switch is never correct — the
      -- unresolved cases render the loud marker instead (#44).
      let unlowered : LExpr := .var "(unsupported: switch not lowerable)"
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
        .var "(unsupported: throw without @throws)"
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
      let emitted :=
        ((emitRefinementLiteral env.aliasEnv env.retTy e)
          <|> (emitLiteralAsCtor env.aliasEnv env.retTy e))
          |>.getD (emitExprEnv env e)
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
      -- #26: a non-canonical `for` desugars at the AST level to
      -- `init; while (test) { body; update }` and re-enters this function,
      -- reusing the while lowering (and `emitVarDeclDo`'s `let mut`
      -- routing for the init declarator). A missing test is `while true`.
      -- The init binding outliving the loop in the Lean block is safe:
      -- shadowing rejection (TH0032) keeps any same-named outer binding
      -- out, so no later read can resolve to the loop variable.
      | .notLowerable =>
          match s with
          | .forStmt fb init test update body =>
              if LoopShape.generalForDesugarable s
                  && !(LoopShape.hasLabeledBreakOrContinue body) then
                let initStmts : List Statement := match init with
                  | none => []
                  | some (.inl e) => [.exprStmt fb e]
                  | some (.inr vd) => [.variableDecl vd]
                let testE : Expression := match test with
                  | some e => e
                  | none => .literal fb (.boolean true) "true"
                let bodyStmts := blockStmts body
                  ++ (match update with
                      | some u => [.exprStmt fb u]
                      | none => [])
                emitBodyDo env info
                  (initStmts
                    ++ .whileStmt fb testE (.blockStmt fb bodyStmts) :: rest)
              else unloweredDoStmt
          | _ => unloweredDoStmt
  -- #26 loop lowering: `while (c) body` → `while c do …`; `do body while (c)`
  -- → `repeat … until !(c)` (TS loops WHILE the test holds, Lean loops UNTIL
  -- it does). EscapeAnalysis admits only lowerable shapes into do-mode —
  -- labeled break/continue, and a do-while whose loop-level `continue` would
  -- skip the until-check, were poisoned upstream; the re-checks here are
  -- defence-in-depth against phase drift, like the for cases above.
  | .whileStmt _ test body :: rest =>
      if LoopShape.hasLabeledBreakOrContinue body then unloweredDoStmt
      else
        .whileDo (emitExprEnv env test) (emitBodyDo env info (blockStmts body))
          :: emitBodyDo env info rest
  | .doWhileStmt _ body test :: rest =>
      if LoopShape.hasLabeledBreakOrContinue body
          || LoopShape.hasOwnUnlabeledContinue body then unloweredDoStmt
      else
        .repeatUntilDo (emitBodyDo env info (blockStmts body))
            (.app (.var "not") [emitExprEnv env test])
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
            | some e =>
                ((emitRefinementLiteral env.aliasEnv targetTy e)
                  <|> (emitLiteralAsCtor env.aliasEnv targetTy e))
                  |>.getD (emitExprEnv env e)
            | none   => .var "()"
          let env' :=
            match typeAnnotation with
            | some t => { env with bindingEnv := env.bindingEnv.insert id.name t }
            | none   => env
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

/-- Normalize a TSType for use in emission: convert nullable unions to `option`. -/
private def normalizeForEmit : TSType → TSType
  | .union types =>
    match normalizeNullableUnion types with
    | some optTy => optTy
    | none => .union types
  | other => other

/-- Emit a TypeScript function declaration. `total = true` emits a `def`
    (forcing Lean's termination checker); otherwise `partial def`. -/
def emitFuncDecl (aliasEnv : Std.HashMap String TSType) (name : String) (typeParams : List String)
    (params : List (String × TSType)) (retTy : TSType)
    (body : Statement) (throws : List String := [])
    (funcThrowsEnv : Std.HashMap String (List String) := {})
    (funcParamTypes : Std.HashMap String (List TSType) := {})
    (total : Bool := false) : Option LDecl :=
  let normalizedRetTy := normalizeForEmit retTy
  let normalizedParams := params.map fun (n, t) => (n, normalizeForEmit t)
  let bindingEnv : Std.HashMap String TSType :=
    normalizedParams.foldl (fun m (n, t) => m.insert n t) {}
  let env : EmitEnv := { aliasEnv, bindingEnv, retTy := some normalizedRetTy,
                         throwTypes := throws, funcThrowsEnv, funcParamTypes }
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
      let core := if doStmtsTerminate core then core else core ++ [.ret (.var "()")]
      .idRunDo core
    else
      emitBodyEnv env stmts
  let leanParams := normalizedParams.map fun (n, t) => (n, emitType t)
  let leanRetTy :=
    if throws.isEmpty then emitType normalizedRetTy
    else buildExceptRetTy throws (emitType normalizedRetTy)
  some (.def_ name typeParams leanParams leanRetTy bodyExpr (isPartial := !total))

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
    | .importDecl _ source _ =>
        if source.startsWith "./" || source.startsWith "../" then
          let m := pathToLeanModule source
          if m.isEmpty then none else some m
        else none
    | _ => none

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

/-- Walk the program and produce a Lean module string. -/
def emit (prog : TSProgram) (moduleName : String) : String :=
  let resolvedAliases := resolveAliases prog.body
  let funcThrowsEnv := buildFuncThrowsEnv prog.body
  let funcParamTypes := buildFuncParamTypesEnv prog.body
  let tsImports := collectImports prog.body
  -- Top-level binding env: every `annotatedVarDecl` with a declared type
  -- contributes a binding so that `console.log(a + b)` can detect refinement
  -- operands and project `.val` accordingly.
  let topBindingEnv : Std.HashMap String TSType := prog.body.foldl (fun acc ts =>
    match ts with
    | .annotatedVarDecl _ _ name (some typeAnn) _ => acc.insert name typeAnn.type
    | .annotatedVarDecl _ _ name none (some (.arrayExpr _ elems)) =>
        acc.insert name (.tuple (List.replicate elems.length .any))
    | .annotatedVarDecl _ _ name none (some (.literal _ (.string _) _)) =>
        acc.insert name .string
    | _ => acc) {}
  let topEnv : EmitEnv := { aliasEnv := resolvedAliases, bindingEnv := topBindingEnv,
                            funcThrowsEnv, funcParamTypes }
  let optToList : Option LDecl → List LDecl := fun
    | some d => [d]
    | none => []
  -- Pair each top-level item with its index so that the dite-binder counter
  -- can be seeded distinctly per item (two top-level `if`s would otherwise
  -- both start at `h0` and collide). `16` leaves generous headroom for the
  -- number of `dite` binders any single top-level statement could introduce.
  let decls : List LDecl := prog.body.zipIdx.flatMap fun (ts, idx) =>
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
        optToList (emitFuncDecl resolvedAliases name (typeParamNames tps) simpleParams retTy body throws funcThrowsEnv funcParamTypes total)
    | .annotatedVarDecl _ _kind name typeAnn (some init) =>
        match init with
        | .arrowFunctionExpr _ arrowParams body _isExpr async arrowRetAnn =>
            if async then []
            else
              -- Arrow's own return annotation wins; var-decl annotation is the fallback.
              let effectiveAnn := arrowRetAnn <|> typeAnn
              let (simpleParams, retTy) := arrowFuncParts arrowParams effectiveAnn
              optToList (emitFuncDecl resolvedAliases name [] simpleParams retTy (match body with
                | .inl e  => .blockStmt {} [.returnStmt {} (some e)]
                | .inr s  => s) [] funcThrowsEnv funcParamTypes)
        | other =>
            -- Non-arrow const: prefer the user's annotation when present.
            -- Otherwise, attempt to infer a Lean type from the initializer
            -- shape (e.g. `[10, 20, 30]` → `Array Float`). Without a usable
            -- type, the decl is silently skipped (the type-checker will have
            -- diagnosed the use-site already).
            match typeAnn with
            | some ann =>
                let initExpr :=
                  (emitRefinementLiteral resolvedAliases (some ann.type) other)
                    <|> (emitLiteralAsCtor resolvedAliases (some ann.type) other)
                    |>.getD (emitExprEnv topEnv other)
                [.def_ name [] [] (emitType ann.type) initExpr]
            | none =>
                -- Unannotated `const x = init`: emit `def x := init` and
                -- let Lean infer the type. Skip when the initializer is
                -- something we don't yet know how to lower (a placeholder
                -- `(unsupported expr)` would not elaborate).
                let initExpr := emitExprEnv topEnv other
                [.def_ name [] [] .inferred initExpr]
    -- Bare top-level call expression like `asBit(2);`. The TS surface
    -- semantics is "evaluate for its side effect (throw)". Lean has no
    -- direct top-level statements, so we emit `#eval (...)` so any panic
    -- surfaces at module elaboration. Skip when the callee is `console.log`
    -- (handled below) or an identifier we haven't seen.
    | .js (.exprStmt _ (call@(.callExpr _ (.identifier _ fname) callArgs _))) =>
        -- Bare `f(args);` at top level is a side-effect statement. For the
        -- throwing prelude constructors `asInteger`/`asNatural`/`asByte`/
        -- `asBit`, emit the IO-effect form which `IO.Process.exit 1`s on
        -- failure (so the harness sees a nonzero exit, matching tsx's
        -- RangeError). For `@throws` callees, match on the Except. Otherwise
        -- evaluate the call for any panic side-effect from `as<T>`.
        let asEffectName : Option String := match fname with
          | "asInteger" => some "asIntegerEffect"
          | "asNatural" => some "asNaturalEffect"
          | "asByte" => some "asByteEffect"
          | "asBit" => some "asBitEffect"
          | _ => none
        match asEffectName with
        | some effFn =>
            let leanArgs := callArgs.map (emitExprEnv topEnv)
            [.eval_ (.app (.var effFn) leanArgs)]
        | none =>
        match funcThrowsEnv.get? fname with
        | some _ =>
            let callLExpr := emitExprEnv topEnv call
            let okArm : LPattern × LExpr := (.ctor "ok" [.wildcard], .app (.var "pure") [.var "()"])
            let errArm : LPattern × LExpr := (.ctor "error" [.wildcard],
              .app (.var "panic!") [.str s!"throw from {fname}"])
            [.eval_ (.match_ callLExpr [okArm, errArm])]
        | none =>
            [.eval_ (emitExprEnv topEnv call)]
    -- Top-level `console.log(arg)` → `#eval consoleLog arg`. When `arg` is a
    -- call to a `@throws` function, match on the Except to extract the value.
    -- Multi-arg `console.log(a, b, c)` lowers to `consoleLogN [show a, …]`
    -- which prints space-separated values, matching JS behavior.
    | .js (.exprStmt _ (.callExpr _
        (.memberExpr _ (.identifier _ "console") (.identifier _ "log") false _)
        args _)) =>
        match args with
        | [arg] =>
            let calleeNameOpt : Option String := match arg with
              | .callExpr _ (.identifier _ fname) _ _ => funcThrowsEnv.get? fname |>.map (fun _ => fname)
              | _ => none
            let argExpr := emitExprEnv topEnv arg
            match calleeNameOpt with
            | some _fname =>
                let okArm : LPattern × LExpr := (.ctor "ok" [.var "v__"], .app (.var "consoleLog") [.var "v__"])
                let errArm : LPattern × LExpr := (.ctor "error" [.wildcard], .app (.var "pure") [.var "()"])
                [.eval_ (.match_ argExpr [okArm, errArm])]
            | none =>
                [.eval_ (.app (.var "consoleLog") [argExpr])]
        | _ :: _ =>
            -- Multi-arg console.log: lower each arg to `JSShow.jsShow` and
            -- intercalate with spaces, then `IO.println`. We construct this
            -- via Thales.TS.consoleLogN, defined alongside `consoleLog` in
            -- Runtime.lean.
            let argExprs := args.map (emitExprEnv topEnv)
            let listLit := mkListLit (argExprs.map fun e => .app (.var "JSShow.jsShow") [e])
            [.eval_ (.app (.var "consoleLogN") [listLit])]
        | _     => []
    -- Top-level `try { console.log(f(args)) } catch (e) { console.log(g) }`,
    -- where `f` is `@throws`, lowers to a `#eval match` over the Except result.
    | .js (.tryStmt _
        (tryBlock)
        (some (CatchClause.mk _ paramOpt catchBody _catchType))
        _finalizer) =>
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
              some (.app (.var "consoleLog") [emitExprEnv topEnv catchArg])
          | _ => none
        optToList <| tryStmts.findSome? fun s =>
          match s with
          | .exprStmt _ (.callExpr _
              (.memberExpr _ (.identifier _ "console") (.identifier _ "log") false _)
              [(.callExpr _ (.identifier _ calleeName) _ _)] _) =>
              match funcThrowsEnv.get? calleeName with
              | some _ =>
                  let callLExpr := match s with
                    | .exprStmt _ (.callExpr _ _ [cArg] _) => emitExprEnv topEnv cArg
                    | _ => .var "()"
                  let okArm : LPattern × LExpr :=
                    (.ctor "ok" [.var "v__"], .app (.var "consoleLog") [.var "v__"])
                  let errArm : LPattern × LExpr :=
                    (.ctor "error" [.var catchVar],
                     catchEffect.getD (.app (.var "pure") [.var "()"]))
                  some (.eval_ (.match_ callLExpr [okArm, errArm]))
              | none => none
          | _ => none
    -- Top-level `if (cond) { … }` lowers to `#eval <IO action>`, preserving
    -- `console.log`s inside the branch and any refinement-narrowing. Seed the
    -- dite-binder counter per item so distinct top-level `if`s get distinct
    -- binder names (`h0`, `h16`, …) and never collide.
    | .js (.ifStmt _ cond thn elsOpt) =>
        let ifEnv : EmitEnv := { topEnv with diteBinderCounter := idx * 16 }
        [.eval_ (emitIfIO ifEnv cond thn elsOpt [])]
    | _ => []
  let body : LDecl :=
    if moduleName.isEmpty then .namespace_ "Input" decls
    else .namespace_ moduleName decls
  renderModule {
    imports := "Thales.TS.Runtime" :: tsImports
    opens := ["Thales.TS"]
    decls := [body]
  }

end Thales.Emit
