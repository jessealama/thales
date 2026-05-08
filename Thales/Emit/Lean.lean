import Thales.TypeCheck.TSAST
import Thales.TypeCheck.Context
import Thales.TypeCheck.Generic
import Thales.TypeCheck.IndexBounds
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
  -- Function name → declared parameter types. Used at call sites to coerce
  -- numeric literal arguments into refinement-typed slots.
  funcParamTypes : Std.HashMap String (List TSType) := {}
  -- In-scope `(idxVar, arrayName, hypothesisName)` triples carrying the
  -- `i.toNat < arr.size` proof bound by an enclosing `dite`.
  boundsProofs  : List (String × String × String) := []
  -- Counter for fresh `dite` binder names (`h0`, `h1`, …).
  diteBinderCounter : Nat := 0

/-- Resolve a TSType through one level of type-alias references. -/
private def resolveTypeAlias (env : EmitEnv) : TSType → TSType
  | .ref name _ =>
    match env.aliasEnv.get? name with
    | some resolved => resolved
    | none => .ref name []
  | .paren inner => resolveTypeAlias env inner
  | other => other

/-- Strip nested `paren` wrappers. -/
private partial def stripParen : TSType → TSType
  | .paren inner => stripParen inner
  | other => other

/-- If every branch of a union shares one underlying primitive (all string
    literals, or all numeric literals, or all boolean literals), return that
    primitive. Used to lower `1 | 2 | 3` to `Float`, `"a" | "b"` to `String`,
    etc. — the constraint is lost on the Lean side, but the resulting type
    is what value-level returns can elaborate against. -/
private def commonLiteralPrimitive (branches : List TSType) : Option LType :=
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
    (i.e. `.matched-ctor`). Returns `none` to fall through to the normal
    expression path. -/
private def emitLiteralAsCtor
    (aliasEnv : Std.HashMap String TSType) (targetTy : Option TSType)
    (expr : Expression) : Option LExpr := do
  let ty ← targetTy
  let aliasName ← match stripParen ty with
    | .ref n [] => some n
    | _ => none
  -- Expect the alias body to be a same-primitive literal union.
  let aliasBody ← aliasEnv[aliasName]?
  let branches ← match stripParen aliasBody with
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

/-- Rewrite `.ref "Integer" []` / `"Natural"` / etc. to the `.refinement`
    form. The emit only sees `typeAliasDecl` for in-file aliases, so prelude
    refinement names are matched directly. -/
private def normalizeRefinementRef (ty : TSType) : TSType :=
  match ty with
  | .ref name [] =>
      match RefinementKind.ofTypeName? name with
      | some k => .refinement k
      | none => ty
  | _ => ty

/-- Resolve a target type to a refinement kind, following one level of
    type-alias indirection through `aliasEnv`. Used to detect refinement
    targets like `Byte` (a TS alias tagged `.refinement` by the type-checker
    via the prelude shim). -/
private partial def resolveRefinementTarget
    (aliasEnv : Std.HashMap String TSType) : TSType → Option RefinementKind
  | .refinement k => some k
  | .paren inner => resolveRefinementTarget aliasEnv inner
  | .ref name [] =>
      match RefinementKind.ofTypeName? name with
      | some k => some k
      | none =>
          match aliasEnv[name]? with
          | some inner => resolveRefinementTarget aliasEnv (stripParen inner)
          | none => none
  | _ => none

/-- If the target type resolves to a refinement and the expression is a
    numeric literal, emit `⟨lit, by native_decide⟩`. Out-of-range literals
    are rejected upstream by TH0080. -/
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

/-- True when the named binding holds a refinement-typed value, so an
    `.identifier` expression referring to it should be projected via
    `.val` in arithmetic contexts. -/
private def isRefinementBinding (env : EmitEnv) (name : String) : Bool :=
  match env.bindingEnv.get? name with
  | some (.refinement _) => true
  | some (.ref tyName []) =>
      (RefinementKind.ofTypeName? tyName).isSome ||
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

/-- Bounds-condition shape recognized for `dite` rewriting and for collecting
    in-scope bounds facts: `i < xs.length` (or its mirror), `xs.length > 0`
    (or its mirror), or anything else. -/
inductive BoundsCondKind where
  | indexBound (idxVar : String) (arrName : String)
  | lengthPos (arrName : String)
  | other

/-- Classify a single binary-expr bounds-condition. -/
private def classifyBoundsCond (env : EmitEnv) : Expression → BoundsCondKind
  | .binaryExpr _ .lt (.identifier _ idxVar) right =>
      match isLengthMember right with
      | some arr =>
          if isRefinementBinding env idxVar then .indexBound idxVar arr else .other
      | none => .other
  | .binaryExpr _ .gt left (.identifier _ idxVar) =>
      match isLengthMember left with
      | some arr =>
          if isRefinementBinding env idxVar then .indexBound idxVar arr else .other
      | none => .other
  | .binaryExpr _ .gt left (.literal _ (.number n) _) =>
      if n == 0.0 then (isLengthMember left).elim .other .lengthPos else .other
  | .binaryExpr _ .lt (.literal _ (.number n) _) right =>
      if n == 0.0 then (isLengthMember right).elim .other .lengthPos else .other
  | _ => .other

/-- Walk a logical conjunction and gather every in-bounds fact it carries. -/
private partial def collectCondBounds (env : EmitEnv) :
    Expression → List (String × String)
  | .logicalExpr _ .«and» l r => collectCondBounds env l ++ collectCondBounds env r
  | other =>
      match classifyBoundsCond env other with
      | .indexBound i a => [(i, a)]
      | _ => []

/-- Detect a prelude refinement predicate call (`isInteger(x)` etc., or
    `Number.isSafeInteger(x)` aliased to `isInteger`). Returns the var name
    being narrowed and the resulting kind. -/
private def detectRefinementPredicate : Expression → Option (String × RefinementKind)
  | .callExpr _ (.identifier _ name) [.identifier _ v] _ =>
      (RefinementKind.ofPredicate? name).map (v, ·)
  | .callExpr _ (.memberExpr _ (.identifier _ "Number") (.identifier _ "isSafeInteger") false _)
              [.identifier _ v] _ =>
      some (v, .integer)
  | _ => none

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
  -- For arithmetic/relational ops, project `.val` off refinement operands.
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
  -- Call expression. Numeric-literal args matching refinement-typed
  -- parameters get wrapped in Subtype constructors; `Math.abs(integer)`
  -- dispatches to `Math.absI` so the result is `Natural`.
  | .callExpr _ callee args _ =>
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
  -- JS Number/Math static methods → Lean Float helpers.
  | .memberExpr _ (.identifier _ "Number") (.identifier _ "isSafeInteger") false _ =>
      .var "Float.isSafeInteger"
  | .memberExpr _ (.identifier _ "Number") (.identifier _ "isInteger") false _ =>
      .var "Float.isInteger"
  | .memberExpr _ (.identifier _ "Number") (.identifier _ "isNaN") false _ =>
      .var "isNaN"
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
  -- `arr.length` / `s.length` lower to a `Natural` (via `toNaturalSize` /
  -- `toNaturalLength`). `emitCondForDite` bypasses this for `dite` conds.
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
      let kind := IndexBounds.classify obj idx env.bindingEnv
                    (env.boundsProofs.map fun (idxV, arrN, _) =>
                      { indexVar := idxV, arrayName := arrN : IndexBounds.BoundsFact })
      let arrExpr := emitExprEnv env obj
      -- Coerce the index to `Nat` for Lean's `Array` indexing typeclass.
      let idxAsNat : LExpr := match idx with
        | .literal _ (.number n) _ =>
            if n ≥ 0.0 && n == n.floor then .nat n.toUInt32.toNat
            else emitExprEnv env idx
        | .identifier _ name =>
            if isRefinementBinding env name then .proj (.var name) "toNat"
            else
              .proj (.proj (.var name) "toUInt64") "toNat"
        | _ => .proj (.proj (emitExprEnv env idx) "toUInt64") "toNat"
      match kind with
      | .byDecide =>
          .indexProof arrExpr idxAsNat "by native_decide"
      | .byHypothesis =>
          match idx, obj with
          | .identifier _ idxName, .identifier _ arrName =>
              let proofName : Option String := env.boundsProofs.findSome? fun (iv, an, hn) =>
                if iv == idxName && an == arrName then some hn else none
              match proofName with
              | some h => .indexProof arrExpr idxAsNat h
              | none => .indexOpt arrExpr idxAsNat
          | _, _ => .indexOpt arrExpr idxAsNat
      | .unknown =>
          -- Length-positive specialization: a preceding `if (xs.length > 0)`
          -- registers a `("__zero", xs, h)` proof that discharges `xs[0]`.
          match idx, obj with
          | .literal _ (.number n) _, .identifier _ arrName =>
              if n == 0.0 then
                let proofName : Option String := env.boundsProofs.findSome? fun (iv, an, hn) =>
                  if iv == "__zero" && an == arrName then some hn else none
                match proofName with
                | some h => .indexProof arrExpr idxAsNat h
                | none => .indexOpt arrExpr idxAsNat
              else .indexOpt arrExpr idxAsNat
          | _, _ => .indexOpt arrExpr idxAsNat
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

/-- Emit a condition for `dite`, rewriting bounds shapes to `Nat`-typed
    counterparts (`i < xs.length` → `i.toNat < xs.size`; `xs.length > 0`
    → `0 < xs.size`). -/
partial def emitCondForDite (env : EmitEnv) (cond : Expression) : LExpr :=
  match classifyBoundsCond env cond with
  | .indexBound idxVar arr =>
      .binOp "<" (.proj (.var idxVar) "toNat") (.proj (.var arr) "size")
  | .lengthPos arr =>
      .binOp "<" (.nat 0) (.proj (.var arr) "size")
  | .other => emitExprEnv env cond

/-- Emit declarators as nested `let` bindings. Refinement-targeted literal
    initializers get a Subtype constructor; new bindings extend `env`. -/
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
          -- Synthesize a tuple binding for a literal-array initializer so
          -- the index-bounds analyzer can see the length even without a
          -- type annotation.
          let inferredFromInit : Option TSType := match init with
            | some (.arrayExpr _ elems) =>
                some (.tuple (List.replicate elems.length .any))
            | _ => none
          let env' :=
            match typeAnnotation with
            | some t =>
                { env with bindingEnv := env.bindingEnv.insert id.name (normalizeRefinementRef t) }
            | none =>
              match inferredFromInit with
              | some t => { env with bindingEnv := env.bindingEnv.insert id.name t }
              | none => env
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
      -- The else-continuation: shared by every emission shape (dite, ite, match).
      let elsCont : LExpr := match elsOpt with
        | some els => emitBodyEnv env (els :: rest)
        | none => emitBodyEnv env rest
      let plainIte : LExpr :=
        .ite (emitExprEnv env cond) (emitBodyEnv env (thn :: rest)) elsCont
      let hName := s!"h{env.diteBinderCounter}"
      -- `if (isInteger(x))` → `if h : isInteger x = true then let x : Integer := ⟨x, h⟩ in …`
      match detectRefinementPredicate cond with
      | some (varName, kind) =>
          let condExpr : LExpr :=
            .binOp "=" (.app (.var kind.predicate) [.var varName]) (.bool true)
          let env' : EmitEnv :=
            { env with
                bindingEnv := env.bindingEnv.insert varName (.refinement kind),
                diteBinderCounter := env.diteBinderCounter + 1 }
          let shadowed : LExpr :=
            .letE varName (some (.const kind.name))
              (.anonCtor [.var varName] hName) (emitBodyEnv env' (thn :: rest))
          .dite_ hName condExpr shadowed elsCont
      | none =>
      -- Bounds-fact dite rewrite. When the cond is `i < xs.length`,
      -- `xs.length > i`, or `xs.length > 0`, emit `if h : <Nat-cond> then …`
      -- and stash the proof in `env.boundsProofs` for the indexing emit.
      let boundsFacts := collectCondBounds env cond
      let mkBoundsDite (idxVar arrName : String) : LExpr :=
        let env' : EmitEnv :=
          { env with
              boundsProofs := (idxVar, arrName, hName) :: env.boundsProofs,
              diteBinderCounter := env.diteBinderCounter + 1 }
        .dite_ hName (emitCondForDite env cond) (emitBodyEnv env' (thn :: rest)) elsCont
      match boundsFacts, classifyBoundsCond env cond with
      | [(idxVar, arrName)], _ => mkBoundsDite idxVar arrName
      -- A standalone `xs.length > 0` (synthetic indexVar `__zero`).
      | [], .lengthPos arrName => mkBoundsDite "__zero" arrName
      | _, _ =>
      match nullCheckVar cond with
      | some varName =>
          match env.bindingEnv.get? varName with
          | some (.option _) =>
              let noneArm := (LPattern.ctor "none" [], emitBodyEnv env [thn])
              let someArm := (LPattern.ctor "some" [.var varName], elsCont)
              .match_ (.var varName) [noneArm, someArm]
          | _ => plainIte
      | none => plainIte
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
    (funcParamTypes : Std.HashMap String (List TSType) := {})
    (total : Bool := false) : Option LDecl :=
  let normalizedRetTy := normalizeForEmit retTy
  let normalizedParams := params.map fun (n, t) => (n, normalizeForEmit t)
  -- Bare `Integer`/`Natural`/`Byte`/`Bit` are rewritten to `.refinement`
  -- so the index-bounds analyzer recognizes them.
  let bindingEnv : Std.HashMap String TSType :=
    normalizedParams.foldl (fun m (n, t) => m.insert n (normalizeRefinementRef t)) {}
  let env : EmitEnv := { aliasEnv, bindingEnv, retTy := some normalizedRetTy,
                         throwTypes := throws, funcThrowsEnv, funcParamTypes }
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

/-- Build per-function throws and parameter-types maps in a single pass. -/
private def buildFuncEnvs (body : List TSStatement) :
    Std.HashMap String (List String) × Std.HashMap String (List TSType) :=
  body.foldl (fun (throws, params) ts =>
    match ts with
    | .annotatedFuncDecl _ name _ ps _ _ _ _ throwsAnn _ =>
        let throws' := match throwsAnn with
          | .declared (t :: ts') => throws.insert name (t :: ts')
          | .declared [] | .absent => throws
        let paramTys := ps.map fun (_, annot, _, _) =>
          match annot with | some a => a.type | none => TSType.any
        (throws', params.insert name paramTys)
    | _ => (throws, params)) ({}, {})

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
  let (funcThrowsEnv, funcParamTypes) := buildFuncEnvs prog.body
  let tsImports := collectImports prog.body
  -- Top-level binding env: annotated decls record their type so refinement
  -- operands get `.val`-projected; unannotated literal-array decls get a
  -- synthetic tuple binding so the index-bounds analyzer sees their length.
  let topBindingEnv : Std.HashMap String TSType := prog.body.foldl (fun acc ts =>
    match ts with
    | .annotatedVarDecl _ _ name (some typeAnn) _ =>
        acc.insert name (normalizeRefinementRef typeAnn.type)
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
    -- Bare top-level call (`asBit(2);`, `f();`, …) lowers to `#eval`.
    -- Throwing prelude constructors use their IO-effect mirror so a
    -- runtime failure exits non-zero, matching tsx's RangeError.
    | .js (.exprStmt _ (call@(.callExpr _ (.identifier _ fname) callArgs _))) =>
        -- `asInteger`/`asNatural`/`asByte`/`asBit` → `…Effect` IO mirror.
        let asEffectName : Option String :=
          RefinementKind.all.findSome? fun k =>
            if fname == s!"as{k.name}" then some s!"{fname}Effect" else none
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
            -- Multi-arg console.log: render each via JSShow and intercalate spaces.
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
