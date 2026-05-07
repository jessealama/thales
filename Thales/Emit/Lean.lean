import Thales.TypeCheck.TSAST
import Thales.TypeCheck.Context
import Thales.TypeCheck.Generic
import Thales.Emit.LeanSyntax
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
  -- Bounds proofs in scope: a list of `(idxVar, arrayName, hypothesisName)`
  -- entries. The hypothesis is the dite-bound proof
  -- `<idxVar>.toNat < <arrayName>.size`. P2 indexing in `xs[i]'h` consults
  -- this list to discharge its bounds proof. Populated by Task 5.3 when
  -- entering a `dite` from an in-bounds-fact-bearing `if`.
  boundsProofs  : List (String × String × String) := []
  -- Counter used to generate unique dite-binder names. Bumped each time
  -- a fresh `h_i` is introduced.
  diteBinderCounter : Nat := 0

/-- Resolve a TSType through one level of type-alias references. -/
private def resolveTypeAlias (env : EmitEnv) : TSType → TSType
  | .ref name _ =>
    match env.aliasEnv.get? name with
    | some resolved => resolved
    | none => .ref name []
  | .paren inner => resolveTypeAlias env inner
  | other => other

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

/-- Extract the null-checked variable name from an `x === null` or `x === undefined` condition.
    Returns `some varName` for `x === null`, `x === undefined`, `null === x`, `undefined === x`.
    Returns `none` for other conditions. -/
private def nullCheckVar : Expression → Option String
  | .binaryExpr _ .seq (.identifier _ varName) (.literal _ .null _) => some varName
  | .binaryExpr _ .eq (.identifier _ varName) (.literal _ .null _) => some varName
  | .binaryExpr _ .seq (.literal _ .null _) (.identifier _ varName) => some varName
  | .binaryExpr _ .eq (.literal _ .null _) (.identifier _ varName) => some varName
  | .binaryExpr _ .seq (.identifier _ varName) (.identifier _ "undefined") =>
    if varName != "undefined" then some varName else none
  | .binaryExpr _ .eq (.identifier _ varName) (.identifier _ "undefined") =>
    if varName != "undefined" then some varName else none
  | .binaryExpr _ .seq (.identifier _ "undefined") (.identifier _ varName) =>
    if varName != "undefined" then some varName else none
  | .binaryExpr _ .eq (.identifier _ "undefined") (.identifier _ varName) =>
    if varName != "undefined" then some varName else none
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
    `undefined` identifier, leave it as `.none`. Otherwise wrap in `.some`. -/
private def wrapReturn (retTy : Option TSType) (e : LExpr) : LExpr :=
  match retTy with
  | some (.option _) =>
    match e with
    | .ctor "none" [] => e
    | .var "undefined" => .ctor "none" []
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

/-- Recognize an `arr.length` expression. -/
private def isLengthMember : Expression → Option String
  | .memberExpr _ (.identifier _ arr) (.identifier _ "length") false _ => some arr
  | _ => none

/-- Detect a bounds-fact comparison that triggers P2 indexing. Returns the
    `(idxVar, arrayName)` pair when the cond is `i < xs.length` or
    `xs.length > i` (where `i` is a refinement-typed identifier in `env`,
    and `xs` is an array/tuple binding). -/
private def detectBoundsFact (env : EmitEnv)
    : Expression → Option (String × String)
  | .binaryExpr _ .lt (.identifier _ idxVar) right =>
      match isLengthMember right with
      | some arr =>
          if isRefinementBinding env idxVar then some (idxVar, arr) else none
      | none => none
  | .binaryExpr _ .gt left (.identifier _ idxVar) =>
      match isLengthMember left with
      | some arr =>
          if isRefinementBinding env idxVar then some (idxVar, arr) else none
      | none => none
  | _ => none

/-- Detect a positive-length cond `xs.length > 0`. Returns the array name. -/
private def detectLengthPositive : Expression → Option String
  | .binaryExpr _ .gt left (.literal _ (.number n) _) =>
      if n == 0.0 then isLengthMember left else none
  | .binaryExpr _ .lt (.literal _ (.number n) _) right =>
      if n == 0.0 then isLengthMember right else none
  | _ => none

/-- Walk a logical-conjunction expression and gather the set of in-bounds
    facts it carries (left-to-right). Refinement-narrowing predicates
    `isNatural(i)`/`isInteger(i)` are also collected as side guards
    because Task 5.6 emits them as a `dite` shadow-let; the bounds
    detection here treats their conjunction with `i < xs.length` as a
    bounds fact under the post-narrowed type. -/
private partial def collectCondBounds (env : EmitEnv) :
    Expression → List (String × String)
  | .logicalExpr _ .«and» l r => collectCondBounds env l ++ collectCondBounds env r
  | other =>
      match detectBoundsFact env other with
      | some bf => [bf]
      | none => []

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
  -- `x === null` → x.isNone
  | .binaryExpr _ .seq (.identifier _ varName) (.literal _ .null _) =>
      .proj (.var varName) "isNone"
  | .binaryExpr _ .eq (.identifier _ varName) (.literal _ .null _) =>
      .proj (.var varName) "isNone"
  | .binaryExpr _ .seq (.literal _ .null _) (.identifier _ varName) =>
      .proj (.var varName) "isNone"
  | .binaryExpr _ .eq (.literal _ .null _) (.identifier _ varName) =>
      .proj (.var varName) "isNone"
  | .binaryExpr _ .seq (.identifier _ varName) (.identifier _ "undefined") =>
      .proj (.var varName) "isNone"
  | .binaryExpr _ .eq (.identifier _ varName) (.identifier _ "undefined") =>
      .proj (.var varName) "isNone"
  | .binaryExpr _ .seq (.identifier _ "undefined") (.identifier _ varName) =>
      .proj (.var varName) "isNone"
  | .binaryExpr _ .eq (.identifier _ "undefined") (.identifier _ varName) =>
      .proj (.var varName) "isNone"
  -- `x !== null` → x.isSome
  | .binaryExpr _ .sneq (.identifier _ varName) (.literal _ .null _) =>
      .proj (.var varName) "isSome"
  | .binaryExpr _ .neq (.identifier _ varName) (.literal _ .null _) =>
      .proj (.var varName) "isSome"
  | .binaryExpr _ .sneq (.literal _ .null _) (.identifier _ varName) =>
      .proj (.var varName) "isSome"
  | .binaryExpr _ .neq (.literal _ .null _) (.identifier _ varName) =>
      .proj (.var varName) "isSome"
  | .binaryExpr _ .sneq (.identifier _ varName) (.identifier _ "undefined") =>
      .proj (.var varName) "isSome"
  | .binaryExpr _ .neq (.identifier _ varName) (.identifier _ "undefined") =>
      .proj (.var varName) "isSome"
  | .binaryExpr _ .sneq (.identifier _ "undefined") (.identifier _ varName) =>
      .proj (.var varName) "isSome"
  | .binaryExpr _ .neq (.identifier _ "undefined") (.identifier _ varName) =>
      .proj (.var varName) "isSome"
  -- General binary expressions: when the op is arithmetic/relational, project
  -- `.val` off any refinement-typed identifier operands so the operation
  -- elaborates on plain `Float`.
  | .binaryExpr _ op left right =>
      let lExpr := emitExprEnv env left
      let rExpr := emitExprEnv env right
      if arithBinaryOp op then
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
  -- Call expression
  | .callExpr _ callee args _ =>
      .app (emitExprEnv env callee) (args.map (emitExprEnv env))
  -- Member expression
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
  -- Everything else
  | _ => .var "(unsupported expr)"

/-- Backwards-compatible wrapper used by the few sites that have no env
    available (e.g. the top-level `console.log` lowering). Calls
    `emitExprEnv` with an empty env, which means refinement detection is
    skipped — the caller must guarantee operands are `Float`-typed. -/
partial def emitExpr : Expression → LExpr := emitExprEnv {}

/-- Emit a condition expression in a form Lean will accept as a `Decidable`
    proposition usable in `dite`. Recognizes the bounds-comparison shapes
    we care about and rewrites them to their `Nat`-typed counterparts so
    that `if h : c then ...` elaborates without needing a boolean coercion.
    For `i < xs.length` (with `i` a refinement-typed identifier and `xs` an
    array binding), emits `i.toNat < xs.size`. For `xs.length > 0`, emits
    `0 < xs.size`. Falls back to `emitExprEnv env` for shapes we don't
    rewrite. -/
partial def emitCondForDite (env : EmitEnv) (cond : Expression) : LExpr :=
  match cond with
  | .binaryExpr _ .lt (.identifier _ idxVar) right =>
      match isLengthMember right with
      | some arr =>
          if isRefinementBinding env idxVar then
            .binOp "<" (.proj (.var idxVar) "toNat") (.proj (.var arr) "size")
          else
            emitExprEnv env cond
      | none => emitExprEnv env cond
  | .binaryExpr _ .gt left (.identifier _ idxVar) =>
      match isLengthMember left with
      | some arr =>
          if isRefinementBinding env idxVar then
            .binOp "<" (.proj (.var idxVar) "toNat") (.proj (.var arr) "size")
          else
            emitExprEnv env cond
      | none => emitExprEnv env cond
  | .binaryExpr _ .gt left (.literal _ (.number n) _) =>
      if n == 0.0 then
        match isLengthMember left with
        | some arr => .binOp "<" (.nat 0) (.proj (.var arr) "size")
        | none => emitExprEnv env cond
      else emitExprEnv env cond
  | .binaryExpr _ .lt (.literal _ (.number n) _) right =>
      if n == 0.0 then
        match isLengthMember right with
        | some arr => .binOp "<" (.nat 0) (.proj (.var arr) "size")
        | none => emitExprEnv env cond
      else emitExprEnv env cond
  | _ => emitExprEnv env cond

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
      -- First try the bounds-fact dite rewrite. The cond is checked for an
      -- in-bounds shape (`i < xs.length`, `xs.length > i`, or `xs.length > 0`);
      -- when present, emit `if h : <Nat-cond> then ... else ...` and stash
      -- the proof in `env.boundsProofs` so Task 5.5's P2 indexing can use it.
      let boundsFacts := collectCondBounds env cond
      let lengthPos := detectLengthPositive cond
      if boundsFacts.length = 1 && lengthPos.isNone then
        let (idxVar, arrName) := boundsFacts.head!
        let hName := s!"h{env.diteBinderCounter}"
        let condExpr := emitCondForDite env cond
        let env' : EmitEnv :=
          { env with
              boundsProofs := (idxVar, arrName, hName) :: env.boundsProofs,
              diteBinderCounter := env.diteBinderCounter + 1 }
        let thnExpr := emitBodyEnv env' (thn :: rest)
        let elsExpr := match elsOpt with
          | some els => emitBodyEnv env (els :: rest)
          | none => emitBodyEnv env rest
        .dite_ hName condExpr thnExpr elsExpr
      else if lengthPos.isSome && boundsFacts.isEmpty then
        let arrName := lengthPos.get!
        let hName := s!"h{env.diteBinderCounter}"
        let condExpr := emitCondForDite env cond
        -- Mark the literal index `0` access in the body as P1-equivalent;
        -- record the proof under a synthetic indexVar `__zero` so the
        -- emit-side P2 path can discover it via the literal-zero
        -- specialization in Task 5.5.
        let env' : EmitEnv :=
          { env with
              boundsProofs := ("__zero", arrName, hName) :: env.boundsProofs,
              diteBinderCounter := env.diteBinderCounter + 1 }
        let thnExpr := emitBodyEnv env' (thn :: rest)
        let elsExpr := match elsOpt with
          | some els => emitBodyEnv env (els :: rest)
          | none => emitBodyEnv env rest
        .dite_ hName condExpr thnExpr elsExpr
      else
      match nullCheckVar cond with
      | some varName =>
          match env.bindingEnv.get? varName with
          | some (.option _) | some (.union _) =>
              let isOption := match env.bindingEnv.get? varName with
                | some (.option _) => true
                | _ => false
              if isOption then
                let noneArm := (LPattern.ctor "none" [], emitBodyEnv env [thn])
                let someVarBody := match elsOpt with
                  | some els => emitBodyEnv env (els :: rest)
                  | none => emitBodyEnv env rest
                let someArm := (LPattern.ctor "some" [.var varName], someVarBody)
                .match_ (.var varName) [noneArm, someArm]
              else
                match elsOpt with
                | some els =>
                  .ite (emitExprEnv env cond) (emitBodyEnv env (thn :: rest)) (emitBodyEnv env (els :: rest))
                | none =>
                  .ite (emitExprEnv env cond) (emitBodyEnv env (thn :: rest)) (emitBodyEnv env rest)
          | _ =>
              match elsOpt with
              | some els =>
                .ite (emitExprEnv env cond) (emitBodyEnv env (thn :: rest)) (emitBodyEnv env (els :: rest))
              | none =>
                .ite (emitExprEnv env cond) (emitBodyEnv env (thn :: rest)) (emitBodyEnv env rest)
      | none =>
          match elsOpt with
          | some els =>
            .ite (emitExprEnv env cond) (emitBodyEnv env (thn :: rest)) (emitBodyEnv env (els :: rest))
          | none =>
            -- No else: else-branch is the continuation, encoding the early-return pattern.
            .ite (emitExprEnv env cond) (emitBodyEnv env (thn :: rest)) (emitBodyEnv env rest)
  | .blockStmt _ inner :: rest => emitBodyEnv env (inner ++ rest)
  | .exprStmt _ _ :: rest      => emitBodyEnv env rest
  | .switchStmt _ discriminant cases :: rest =>
      match discriminant with
      | .memberExpr _ (.identifier _ scrutName) (.identifier _ _fieldName) false _ =>
          match env.bindingEnv.get? scrutName with
          | none => emitBodyEnv env rest
          | some rawTy =>
              let resolvedTy := resolveTypeAlias env rawTy
              match resolvedTy with
              | .union branches =>
                  match asDiscriminated branches with
                  | none => emitBodyEnv env rest
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
                      let allArms :=
                        if arms.length >= ctors.length then arms
                        else arms ++ [(.wildcard, .var "unreachable!")]
                      .match_ (.var scrutName) allArms
              | _ => emitBodyEnv env rest
      | _ => emitBodyEnv env rest
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
    (total : Bool := false) : Option LDecl :=
  let normalizedRetTy := normalizeForEmit retTy
  let normalizedParams := params.map fun (n, t) => (n, normalizeForEmit t)
  let bindingEnv : Std.HashMap String TSType :=
    normalizedParams.foldl (fun m (n, t) => m.insert n t) {}
  let env : EmitEnv := { aliasEnv, bindingEnv, retTy := some normalizedRetTy,
                         throwTypes := throws, funcThrowsEnv }
  let bodyExpr := match body with
    | .blockStmt _ stmts => emitBodyEnv env stmts
    | other              => emitBodyEnv env [other]
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
  let tsImports := collectImports prog.body
  -- Top-level binding env: every `annotatedVarDecl` with a declared type
  -- contributes a binding so that `console.log(a + b)` can detect refinement
  -- operands and project `.val` accordingly.
  let topBindingEnv : Std.HashMap String TSType := prog.body.foldl (fun acc ts =>
    match ts with
    | .annotatedVarDecl _ _ name (some typeAnn) _ => acc.insert name typeAnn.type
    | _ => acc) {}
  let topEnv : EmitEnv := { aliasEnv := resolvedAliases, bindingEnv := topBindingEnv,
                            funcThrowsEnv }
  let optToList : Option LDecl → List LDecl := fun
    | some d => [d]
    | none => []
  let decls : List LDecl := prog.body.flatMap fun
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
        optToList (emitFuncDecl resolvedAliases name (typeParamNames tps) simpleParams retTy body throws funcThrowsEnv total)
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
                | .inr s  => s) [] funcThrowsEnv)
        | other =>
            -- Non-arrow const requires a type annotation; without it the Lean type is unknown.
            optToList (typeAnn.map fun ann =>
              let initExpr :=
                (emitRefinementLiteral resolvedAliases (some ann.type) other)
                  <|> (emitLiteralAsCtor resolvedAliases (some ann.type) other)
                  |>.getD (emitExprEnv topEnv other)
              .def_ name [] [] (emitType ann.type) initExpr)
    -- Top-level `console.log(arg)` → `#eval consoleLog arg`. When `arg` is a
    -- call to a `@throws` function, match on the Except to extract the value.
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
