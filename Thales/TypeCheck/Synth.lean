/-
  Thales/TypeCheck/Synth.lean
  Expression type synthesis and checking
-/
import Thales.TypeCheck.TSType
import Thales.TypeCheck.TSAST
import Thales.TypeCheck.Context
import Thales.TypeCheck.Diagnostic
import Thales.TypeCheck.RefinementDiag
import Thales.TypeCheck.Generic
import Thales.TypeCheck.TypeSubstitution
import Thales.TypeCheck.Assignability
import Thales.TypeCheck.TypedExpression
import Thales.TypeCheck.Narrowing
import Thales.TypeCheck.Builtins
import Thales.TypeCheck.AssignTarget

namespace Thales.TypeCheck

open Thales.AST

/-- Look up a property on an object type (or union of object types) -/
private partial def lookupProperty (objType : TSType) (propName : String) (depth : Nat := 0) : TypeCheckM (Option TSType) := do
  if depth > 10 then return none
  match objType with
  | .object members =>
    -- First try direct property match
    let direct := members.findSome? fun
      | .property name ty _ _ => if name == propName then some ty else none
      | .method name params ret _ =>
        if name == propName then some (.function params ret) else none
      | .indexSignature _ _ _ _ => none
    match direct with
    | some ty => return some ty
    | none =>
      -- Fall back to index signature if present
      return members.findSome? fun
        | .indexSignature _ keyType valueType _ =>
          match keyType with
          | .string | .any => some valueType
          | _ => none
        | _ => none
  | .union types =>
    -- For a union, the property is accessible only if ALL members have it (TypeScript semantics).
    -- Return the union of the property types across all members.
    let mut found : List TSType := []
    for t in types do
      match ← lookupProperty t propName depth with
      | some ty => found := found ++ [ty]
      | none => pure ()
    if found.length == types.length then
      match found with
      | [] => return none
      | [single] => return some single
      | multiple =>
        -- Flatten nested unions and deduplicate
        let flat := multiple.flatMap fun t => match t with | .union ts => ts | t => [t]
        return some (.union flat.eraseDups)
    else
      return none  -- Not all union members have the property → type error
  | .intersection types =>
    let mut found : List TSType := []
    for t in types do
      match ← lookupProperty t propName depth with
      | some ty => found := found ++ [ty]
      | none => pure ()
    match found with
    | [] => return none
    | [single] => return some single
    | multiple => return some (.intersection multiple)
  | .typeVar _ _ (some constraint) =>
    let resolved ← resolveTypeGeneric constraint
    lookupProperty resolved propName (depth + 1)
  | .ref .. =>
    let resolved ← resolveTypeGeneric objType
    if resolved != objType then
      lookupProperty resolved propName (depth + 1)
    else
      return none
  | .string | .stringLit _ | .number | .numberLit _ | .boolean | .booleanLit _
  | .refinement _ | .array _ | .tuple _ =>
    return builtinProperty objType propName
  | _ => return none

/-- String members with a correct Lean lowering today. `length` is a property;
    `startsWith`/`endsWith`/`split` lower to byte-identical Lean operations.
    Every other declared `String.prototype` member is rejected (TH0087) — see
    the member-access arm of `synthJSExpr`. -/
def stringMethodSupported (name : String) : Bool :=
  name == "length" || name == "startsWith" || name == "endsWith"
    || name == "split"

/-- Best-effort extraction of a "source name" for a JS expression, used in
    TH0081 diagnostics (`Value '<name>' of type 'number' is not assignable…`).
    Returns the identifier name for a bare identifier, the dotted path for a
    member access, and the empty string otherwise. -/
partial def exprSourceName : Expression → String
  | .identifier _ name => name
  | .memberExpr _ obj (.identifier _ propName) false _ =>
    let parent := exprSourceName obj
    if parent.isEmpty then propName else s!"{parent}.{propName}"
  | _ => ""

/-- Best-effort source-name for a TS expression. -/
partial def tsExprSourceName : TSExpression → String
  | .js e => exprSourceName e
  | .asExpr inner _ => tsExprSourceName inner
  | .satisfiesExpr inner _ => tsExprSourceName inner
  | .nonNullAssert inner => tsExprSourceName inner

/-- Require boolean in positions Lean will branch on: `if`/`while`/
    `do-while`/`for` tests, the ternary test, and the operands of
    `!`/`&&`/`||` (TH0026). JS truthiness — `0`, `''`, `NaN`, `null`,
    `undefined` are falsy — has no Lean-side coercion, so a non-boolean
    here would emit code the Lean stage cannot compile. -/
def requireBooleanCondition (ty : TSType) (loc : Option SourceLocation)
    : TypeCheckM Unit := do
  unless (← isSubtype ty .boolean) do
    emitDiagnostic (.thales (.conditionNotBoolean (formatType ty))) loc

/-- Check if a type contains any typeVar -/
private partial def containsTypeVar : TSType → Bool
  | .typeVar .. => true
  | .option e => containsTypeVar e
  | .array e => containsTypeVar e
  | .tuple es => es.any containsTypeVar
  | .function ps r => ps.any (fun (.mk _ t _ _) => containsTypeVar t) || containsTypeVar r
  | .union ts | .intersection ts => ts.any containsTypeVar
  | .ref _ args => args.any containsTypeVar
  | .object ms => ms.any fun
    | .property _ t _ _ => containsTypeVar t
    | .method _ ps r _ => ps.any (fun (.mk _ t _ _) => containsTypeVar t) || containsTypeVar r
    | .indexSignature _ kt vt _ => containsTypeVar kt || containsTypeVar vt
  | .paren inner => containsTypeVar inner
  | .conditional c e t f => containsTypeVar c || containsTypeVar e || containsTypeVar t || containsTypeVar f
  | .mapped _ c v _ _ => containsTypeVar c || containsTypeVar v
  | _ => false

/-- Collect all unique (typeVar id, TSTypeParam) from params and return type -/
private partial def collectAllTypeVarIds (params : List TSParamType) (retTy : TSType) :
    List (Nat × TSTypeParam) :=
  let acc := params.foldl (fun acc (.mk _ ty _ _) => collectFromType ty acc) []
  collectFromType retTy acc
where
  collectFromType (ty : TSType) (acc : List (Nat × TSTypeParam)) : List (Nat × TSTypeParam) :=
    match ty with
    | .typeVar id name constraint =>
      if acc.any (fun (i, _) => i == id) then acc
      else acc ++ [(id, { name, constraint })]
    | .option e => collectFromType e acc
    | .array e => collectFromType e acc
    | .tuple es => es.foldl (fun a e => collectFromType e a) acc
    | .function ps r =>
      let acc' := ps.foldl (fun a (.mk _ t _ _) => collectFromType t a) acc
      collectFromType r acc'
    | .union ts | .intersection ts => ts.foldl (fun a t => collectFromType t a) acc
    | .ref _ args => args.foldl (fun a t => collectFromType t a) acc
    | .object ms => ms.foldl (fun a m => match m with
      | .property _ t _ _ => collectFromType t a
      | .method _ ps r _ =>
        let a' := ps.foldl (fun acc' (.mk _ t _ _) => collectFromType t acc') a
        collectFromType r a'
      | .indexSignature _ kt vt _ => collectFromType vt (collectFromType kt a)) acc
    | .paren inner => collectFromType inner acc
    | .conditional c e t f =>
      let acc := collectFromType c acc
      let acc := collectFromType e acc
      let acc := collectFromType t acc
      collectFromType f acc
    | .mapped _ c v _ _ => collectFromType v (collectFromType c acc)
    | _ => acc

/-- Returns true if the operator is an arithmetic (non-comparison) binary op -/
private def isArithmeticOp (op : BinaryOperator) : Bool :=
  match op with
  | .add | .sub | .mul | .div | .mod | .exp
  | .bitand | .bitor | .bitxor | .shl | .shr | .ushr => true
  | _ => false

/-- Returns true if the operator is the + (add) operator -/
private def isAddOp (op : BinaryOperator) : Bool :=
  match op with
  | .add => true
  | _ => false

/-- Returns true if the operator is a comparison op returning boolean -/
private def isComparisonOp (op : BinaryOperator) : Bool :=
  match op with
  | .eq | .neq | .seq | .sneq | .lt | .leq | .gt | .geq
  | .instanceof | .«in» => true
  | _ => false

mutual

/-- Synthesize the type of a TS expression -/
partial def synthExpr (expr : TSExpression) (expected : Option TSType := none) : TypeCheckM TypedExpression := do
  match expr with
  | .js e =>
    let typed ← synthJSExpr e expected
    return { expr, type := typed.type, children := #[typed] }
  | .asExpr inner ty =>
    let typedInner ← synthExpr inner
    return { expr, type := ty, children := #[typedInner] }
  | .satisfiesExpr inner _ty =>
    let typedInner ← synthExpr inner
    return { expr, type := typedInner.type, children := #[typedInner] }
  | .nonNullAssert inner =>
    let typedInner ← synthExpr inner
    return { expr, type := typedInner.type, children := #[typedInner] }

/-- Synthesize the type of a JS expression -/
partial def synthJSExpr (expr : Expression) (expected : Option TSType := none) : TypeCheckM TypedExpression := do
  let mk ty children := { expr := .js expr, type := ty, children := children : TypedExpression }
  match expr with
  -- Literals
  -- We keep numeric literals as `.numberLit n` (rather than widening to `.number`)
  -- so that the assignability checker can detect out-of-range literals being
  -- assigned to refinement-typed slots and emit TH0080 instead of TS2322.
  | .literal _ (.number n) _ => return mk (.numberLit n) #[]
  | .literal _ (.string s) _ => return mk (.stringLit s) #[]
  | .literal _ (.boolean b) _ => return mk (.booleanLit b) #[]
  | .literal _ .null _ => return mk .null_ #[]
  | .literal _ (.bigint _) _ => return mk .bigint #[]
  | .literal _ (.regex _ _) _ => return mk .any #[]

  -- Identifier lookup
  | .identifier base name =>
    let binding ← lookupBinding name
    match binding with
    | some ty =>
      checkDefinitelyAssigned name base.loc
      return mk ty #[]
    | none =>
      let ctx ← read
      if ctx.hoistedTopLevelNames.contains name then
        -- Declared later in the file: tsc accepts the forward reference,
        -- but emitted Lean declarations appear in source order.
        emitDiagnostic (.thales (.referencedBeforeDeclaration name)) base.loc
      else
        emitDiagnostic (.identifierNotFound name) base.loc
      return mk .any #[]

  -- Member access: obj.prop
  | .memberExpr base obj (.identifier _ propName) false _ =>
    let objTyped ← synthJSExpr obj
    let resolved ← resolveTypeGeneric objTyped.type
    match ← lookupProperty resolved propName with
    | some ty =>
      -- TH0087: most `String.prototype` methods type-check (they are declared
      -- in `Builtins.stringProperty`) but have no correct Lean lowering — the
      -- emitter would produce a nonexistent `String.<m>` or a semantically
      -- divergent one (e.g. `replace` replaces all, not the first match). Only
      -- `length`/`startsWith`/`endsWith`/`split` are sound today; reject the
      -- rest here, where the receiver type is fully known. `tsc` accepts them.
      let unsupportedStringMethod := match resolved with
        | .string | .stringLit _ => !stringMethodSupported propName
        | _ => false
      if unsupportedStringMethod then
        emitDiagnostic (.thales (.stringMethodNotSupported propName)) base.loc
      return mk ty #[objTyped]
    | none =>
      match resolved with
      | .any => return mk .any #[objTyped]
      | _ =>
        emitDiagnostic (.propertyNotFound propName resolved) base.loc
        return mk .any #[objTyped]

  -- Computed element access: xs[i]. Arrays only; the element type is
  -- `T | undefined` (noUncheckedIndexedAccess is part of the contract,
  -- docs/subset.md). Non-array bases and non-numeric indices are out of
  -- subset (TH0083) — tsc may accept them, so this is a TH, not a TS code.
  | .memberExpr base obj idx true _ =>
    let objTyped ← synthJSExpr obj
    let idxTyped ← synthJSExpr idx
    let resolved ← resolveTypeGeneric objTyped.type
    let idxResolved ← resolveTypeGeneric idxTyped.type
    let idxIsNumeric : Bool := match idxResolved with
      | .number | .numberLit _ | .refinement _ => true
      | _ => false
    match resolved with
    | .array elem =>
      if idxIsNumeric then
        return mk (.option elem) #[objTyped, idxTyped]
      else
        emitDiagnostic (.thales .computedIndexNotArray) base.loc
        return mk .any #[objTyped, idxTyped]
    | .any => return mk .any #[objTyped, idxTyped]
    | _ =>
      emitDiagnostic (.thales .computedIndexNotArray) base.loc
      return mk .any #[objTyped, idxTyped]

  -- Function call: callee(args)
  | .callExpr base callee args _ =>
    let calleeTyped ← synthJSExpr callee
    let resolved ← resolveTypeGeneric calleeTyped.type
    match resolved with
    | .function params retTy =>
      let hasTypeVars := params.any fun (.mk _ ty _ _) => containsTypeVar ty
      let (params, retTy) ← if hasTypeVars then do
        let mut argTypes : List TSType := []
        for arg in args do
          let argTyped ← synthJSExpr arg
          argTypes := argTypes ++ [argTyped.type]
        let typeVarIds := collectAllTypeVarIds params retTy
        let bindings := inferTypeArgs typeVarIds params argTypes
        for (id, param) in typeVarIds do
          if let some constraint := param.constraint then
            if let some inferredTy := bindings[id]? then
              let ok ← isSubtype inferredTy constraint
              if !ok then
                emitDiagnostic (.constraintNotSatisfied inferredTy constraint param.name) base.loc
        let params' := params.map (substituteParam · bindings)
        let retTy' := substitute retTy bindings
        pure (params', retTy')
      else
        pure (params, retTy)
      let requiredCount := (params.filter (fun (.mk _ _ opt rest) => !opt && !rest)).length
      let hasRest := params.any (fun (.mk _ _ _ rest) => rest)
      if args.length < requiredCount then
        emitDiagnostic (.argumentCountMismatch requiredCount args.length) base.loc
      else if !hasRest && args.length > params.length then
        emitDiagnostic (.argumentCountMismatch params.length args.length) base.loc
      -- Refinement-target mismatches surface as TH0080/TH0081; everything
      -- else falls back to TS2345 (argumentTypeMismatch).
      let emitArgMismatch (argIdx : Nat) (srcTy tgtTy : TSType)
          (argExpr : Expression) : TypeCheckM Unit := do
        let resolvedSrc ← resolveTypeGeneric srcTy
        let resolvedTgt ← resolveTypeGeneric tgtTy
        match refinementMismatch? resolvedSrc resolvedTgt (exprSourceName argExpr) with
        | some thKind => emitDiagnostic (.thales thKind) (exprLoc argExpr)
        | none => emitDiagnostic (.argumentTypeMismatch argIdx srcTy tgtTy) (exprLoc argExpr)
      let mut argChildren : Array TypedExpression := #[]
      for i in [:args.length] do
        if i < params.length then
          let (.mk _ paramTy _ isRest) := params[i]!
          let checkTy := if isRest then
            match paramTy with
            | .array elem => elem
            | _ => paramTy
          else paramTy
          let argTyped ← synthJSExpr args[i]!
          argChildren := argChildren.push argTyped
          let ok ← isSubtype argTyped.type checkTy
          if !ok then
            emitArgMismatch i argTyped.type checkTy args[i]!
        else
          match params.getLast? with
          | some (.mk _ paramTy _ true) =>
            let checkTy := match paramTy with | .array elem => elem | _ => paramTy
            let argTyped ← synthJSExpr args[i]!
            argChildren := argChildren.push argTyped
            let ok ← isSubtype argTyped.type checkTy
            if !ok then
              emitArgMismatch i argTyped.type checkTy args[i]!
          | _ =>
            let argTyped ← synthJSExpr args[i]!
            argChildren := argChildren.push argTyped
      -- Refinement-aware overloads: a small fixed table of stdlib calls whose
      -- return type narrows when the argument is a refinement subtype.
      -- Currently: `Math.abs(x)` returns `Natural` when `x : Integer` (and
      -- therefore also when `x : Natural | Byte | Bit` by lattice widening),
      -- and `number` otherwise.
      -- v0.7: `Array.map(cb)` infers return type from the callback body;
      -- `Array.reduce(cb, init)` infers return type from the seed argument.
      let refinedRetTy : TSType ← (do
        match callee, argChildren.toList with
        | .memberExpr _ (.identifier _ "Math") (.identifier _ "abs") false _,
          firstArg :: _ =>
          let resolvedArgTy ← resolveTypeGeneric firstArg.type
          match resolvedArgTy with
          | .refinement _ => return (.refinement .natural : TSType)
          | _ => return retTy
        | .memberExpr _ _ (.identifier _ "map") false _, cbArg :: _ =>
          -- Recover element type from receiver (handles .array and .tuple)
          let recvTy := (calleeTyped.children[0]?).map (·.type)
          let elemTy : Option TSType ← do
            match recvTy with
            | none => pure none
            | some rTy =>
              let resolved ← resolveTypeGeneric rTy
              match resolved with
              | .array e => pure (some e)
              | .tuple [] => pure (some .any)
              | .tuple [single] => pure (some single)
              | .tuple es => pure (some (.union es))
              | _ => pure none
          match elemTy with
          | none => return retTy
          | some elem =>
            -- Unwrap TSExpression to Expression for synthCallbackBody
            let cbExpr : Option Expression := match cbArg.expr with
              | .js e => some e
              | _ => none
            match cbExpr with
            | none => return retTy
            | some e =>
              match ← synthCallbackBody e [elem, .refinement .natural] with
              | some u => return (.array u : TSType)
              | none => return retTy
        | .memberExpr _ _ (.identifier _ "reduce") false _, cbArg :: seedArg :: _ =>
          -- Seed argument determines the accumulator type; the seed type is
          -- always returned as the result type (not inferred from the callback body).
          let seedTy := seedArg.type
          -- Synthesize the callback body to surface internal type errors; the
          -- seed argument's type is the accumulator and the return type.
          -- Note: the element/value parameter is passed as `.any` rather than the
          -- receiver's element type because that type is not yet threaded through
          -- to reduce — do not "fix" this without also wiring up element-type
          -- extraction, or it will produce spurious diagnostics.
          let cbExpr : Option Expression := match cbArg.expr with
            | .js e => some e
            | _ => none
          if let some e := cbExpr then
            let _ ← synthCallbackBody e [seedTy, .any, .refinement .natural]
          return seedTy
        | _, _ => return retTy)
      return mk refinedRetTy (#[calleeTyped] ++ argChildren)
    | .any => return mk .any #[calleeTyped]
    | _ =>
      emitDiagnostic (.notCallable resolved) base.loc
      return mk .any #[calleeTyped]

  -- Binary expressions
  | .binaryExpr _ op left right =>
    let leftTyped ← synthJSExpr left
    let rightTyped ← synthJSExpr right
    -- TH0082: arithmetic/relational operators need definite operands. tsc
    -- accepts e.g. `(string | undefined) + string`, but the emitter has no
    -- JS-coercion lowering for Option operands, so the subset rejects it.
    -- Equality ops are exempt: they are the narrowing primitives.
    let isRelationalOp : Bool := match op with
      | .lt | .leq | .gt | .geq => true
      | _ => false
    let leftResolved ← resolveType leftTyped.type
    let rightResolved ← resolveType rightTyped.type
    if isArithmeticOp op || isRelationalOp then
      if isNullable leftResolved then
        emitDiagnostic (.thales .possiblyUndefinedOperand) (exprLoc left)
      if isNullable rightResolved then
        emitDiagnostic (.thales .possiblyUndefinedOperand) (exprLoc right)
    if isArithmeticOp op then
      if isAddOp op then
        match leftResolved, rightResolved with
        | .string, _ | _, .string | .stringLit _, _ | _, .stringLit _ =>
          return mk .string #[leftTyped, rightTyped]
        | .bigint, _ | _, .bigint => return mk .bigint #[leftTyped, rightTyped]
        | _, _ => return mk .number #[leftTyped, rightTyped]
      else
        -- Non-add arithmetic: preserve bigint if both operands are bigint
        match leftResolved, rightResolved with
        | .bigint, _ | _, .bigint => return mk .bigint #[leftTyped, rightTyped]
        | _, _ => return mk .number #[leftTyped, rightTyped]
    else if isComparisonOp op then
      return mk .boolean #[leftTyped, rightTyped]
    else
      return mk .any #[leftTyped, rightTyped]

  -- Logical expressions
  | .logicalExpr _ op left right =>
    let leftTyped ← synthJSExpr left
    let ctx ← read
    match op with
    | .«and» =>
      -- `&&` is Lean `&&`: both operands must be boolean (TH0026), not
      -- merely the synthesized result.
      requireBooleanCondition leftTyped.type (exprLoc left)
      match Narrowing.extractGuard left with
      | some guard =>
        let narrowed := Narrowing.applyGuard guard ctx.bindings
        let rightTyped ← withScope (Narrowing.bindingsDiff narrowed ctx.bindings) (synthCondition right)
        return { expr := .js expr, type := rightTyped.type, children := #[leftTyped, rightTyped] }
      | none =>
        let rightTyped ← synthCondition right
        return { expr := .js expr, type := rightTyped.type, children := #[leftTyped, rightTyped] }
    | .«or» =>
      -- `||` is Lean `||`: both operands must be boolean (TH0026). A truthy
      -- default (`s || "fallback"`) is out of subset.
      requireBooleanCondition leftTyped.type (exprLoc left)
      match Narrowing.extractGuard left with
      | some guard =>
        let narrowed := Narrowing.applyNegatedGuard guard ctx.bindings
        let rightTyped ← withScope (Narrowing.bindingsDiff narrowed ctx.bindings) (synthCondition right)
        return { expr := .js expr, type := .union [leftTyped.type, rightTyped.type], children := #[leftTyped, rightTyped] }
      | none =>
        let rightTyped ← synthCondition right
        return { expr := .js expr, type := leftTyped.type, children := #[leftTyped, rightTyped] }
    | _ =>
      let rightTyped ← synthJSExpr right
      return { expr := .js expr, type := leftTyped.type, children := #[leftTyped, rightTyped] }

  -- Assignment expressions. Compound `x OP= y` types as `x = x OP y`
  -- (#24): the synthesized RHS is the desugared binary expression, so
  -- checking reuses the binary-op paths (e.g. `s += 1` on a string is
  -- string concatenation, not a raw-RHS-vs-declared mismatch).
  | .assignmentExpr b op left right =>
    let effectiveRHS : Expression :=
      match op.compoundToBinary with
      | some binOp => .binaryExpr b binOp left right
      | none => right
    let rightTyped ← synthJSExpr effectiveRHS
    -- LHS legality (TS2540 / TS2588 / TS2364) — emit before RHS-vs-declared check.
    match ← classifyAssignTarget synthJSExpr left with
    | some kind => emitDiagnostic kind (exprLoc left)
    | none => pure ()
    match left with
    | .identifier _ name =>
      markAssigned name
      -- Validate RHS against declared type
      match ← lookupDeclaredType name with
      | some declaredTy =>
        checkAssignable rightTyped.type declaredTy (exprLoc right) (exprSourceName right)
      | none => pure ()
    | _ => pure ()
    return { expr := .js expr, type := rightTyped.type, children := #[rightTyped] }

  -- Update expressions (++ and --)
  | .updateExpr _ _ arg _ =>
    let argTyped ← synthJSExpr arg
    match ← classifyAssignTarget synthJSExpr arg with
    | some kind => emitDiagnostic kind (exprLoc arg)
    | none => pure ()
    return { expr := .js expr, type := .number, children := #[argTyped] }

  -- Conditional (ternary). The branch join collapses identical types so
  -- e.g. `b ? x : y` with both branches bigint is bigint, not bigint|bigint.
  | .conditionalExpr _ test consequent alternate =>
    let joinTy (a b : TSType) : TSType :=
      match [a, b].eraseDups with
      | [single] => single
      | ts => .union ts
    let testTyped ← synthCondition test
    let ctx ← read
    match Narrowing.extractGuard test with
    | some guard =>
      let thenBindings := Narrowing.applyGuard guard ctx.bindings
      let elseBindings := Narrowing.applyNegatedGuard guard ctx.bindings
      let consTyped ← withScope (Narrowing.bindingsDiff thenBindings ctx.bindings) (synthJSExpr consequent)
      let altTyped ← withScope (Narrowing.bindingsDiff elseBindings ctx.bindings) (synthJSExpr alternate)
      return mk (joinTy consTyped.type altTyped.type) #[testTyped, consTyped, altTyped]
    | none =>
      let consTyped ← synthJSExpr consequent
      let altTyped ← synthJSExpr alternate
      return mk (joinTy consTyped.type altTyped.type) #[testTyped, consTyped, altTyped]

  -- Array literal
  | .arrayExpr _ elements => do
    let elemExpected := match expected with
      | some (.array elemTy) => some elemTy
      | _ => none
    let mut elemTypes : List TSType := []
    let mut children : Array TypedExpression := #[]
    for elem in elements do
      match elem with
      | some e =>
        let typed ← synthJSExpr e elemExpected
        match elemExpected with
        | some elemTy =>
          checkAssignable typed.type elemTy (exprLoc e) (exprSourceName e)
        | none => pure ()
        elemTypes := elemTypes ++ [typed.type]
        children := children.push typed
      | none => elemTypes := elemTypes ++ [.undefined]
    let resultTy := match elemExpected, elemTypes with
      | some eTy, _ => .array eTy
      | none, [] => .array .any
      | none, [ty] => .array ty
      | none, _ => .tuple elemTypes
    return mk resultTy children

  -- Object literal
  | .objectExpr _ properties => do
    let mut memberTypes : List TSObjectMember := []
    let mut children : Array TypedExpression := #[]
    for prop in properties do
      match prop with
      | .regular _ key value _ _ _ =>
        let propName := match key with
          | .identifier _ name => name
          | .literal _ (.string s) _ => s
          | _ => ""
        let memberExpected := match expected with
          | some (.object expectedMembers) =>
            expectedMembers.findSome? fun
              | .property name ty _ _ => if name == propName then some ty else none
              | .method name _ ret _ => if name == propName then some ret else none
              | .indexSignature _ _ _ _ => none
          | _ => none
        let typedValue ← synthJSExpr value memberExpected
        let propTy ← match memberExpected with
          | some tgt => do
            checkAssignable typedValue.type tgt (exprLoc value) (exprSourceName value)
            pure tgt
          | none => pure typedValue.type
        -- Record the target type (not the synthesized value type) so the
        -- synthesized object type matches the expected type; this prevents a
        -- spurious outer-level TS2322 firing alongside the inner TH0081.
        memberTypes := memberTypes ++ [.property propName propTy false false]
        children := children.push typedValue
      | .spread _ arg =>
        let typedArg ← synthJSExpr arg
        children := children.push typedArg
    return mk (.object memberTypes) children

  -- Template literal
  | .templateLiteral _ _ _ => return mk .string #[]

  -- Unary expressions
  | .unaryExpr _ .typeof _ _ => return mk .string #[]
  | .unaryExpr _ .void _ _ => return mk .undefined #[]
  | .unaryExpr _ .neg _ arg =>
    -- tsc types `-x` as bigint when the operand is bigint, number otherwise
    let argTyped ← synthJSExpr arg
    let resolved ← resolveTypeGeneric argTyped.type
    match resolved with
    | .bigint => return mk .bigint #[argTyped]
    | _ => return mk .number #[argTyped]
  | .unaryExpr _ .pos _ _ => return mk .number #[]
  | .unaryExpr _ .bitnot _ _ => return mk .number #[]
  | .unaryExpr _ .not _ arg =>
    -- `!` is Lean `not`: the operand must already be boolean (TH0026).
    let argTyped ← synthCondition arg
    return mk .boolean #[argTyped]

  -- this: bound by the checker inside class ctor/method scopes; any elsewhere
  | .thisExpr _ =>
    match ← lookupBinding "this" with
    | some ty => return mk ty #[]
    | none => return mk .any #[]

  -- new Expr(args): look up class instance type, checking the ctor signature
  | .newExpr base callee args =>
    -- JS global error constructors: recognized by the throws story, typed
    -- `any` here (they are not registered classes).
    let jsGlobalConstructors : List String :=
      ["Error", "RangeError", "TypeError", "SyntaxError", "ReferenceError",
       "EvalError", "URIError", "AggregateError"]
    if let .identifier calleeBase className := callee then
      let ctx ← read
      if ctx.classes[className]?.isNone && !jsGlobalConstructors.contains className then
        -- Not a known class: resolve the callee like any identifier so a
        -- forward reference to a later-declared class draws TH0105 (or
        -- TS2304 if unknown) instead of emitting uncompilable Lean.
        let _ ← synthJSExpr (.identifier calleeBase className)
      if let some info := ctx.classes[className]? then
        let instanceTy := info.instanceType
        if containsTypeVar instanceTy then
          match instanceTy with
          | .object members =>
            let typeVarIds := collectAllTypeVarIds [] (.object members)
            if typeVarIds.isEmpty then
              return mk instanceTy #[]
            let typeVarFields := members.filterMap fun
              | .property _ ty _ _ => if containsTypeVar ty then some ty else none
              | .method _ _ ret _ => if containsTypeVar ret then some ret else none
              | .indexSignature _ _ _ _ => none
            let mut argTypes : List TSType := []
            let mut argChildren : Array TypedExpression := #[]
            for arg in args do
              let typed ← synthJSExpr arg
              argTypes := argTypes ++ [typed.type]
              argChildren := argChildren.push typed
            let pseudoParams := typeVarFields.mapIdx fun i ty =>
              TSParamType.mk s!"arg{i}" ty false false
            let bindings := inferTypeArgs typeVarIds pseudoParams argTypes
            return mk (substitute instanceTy bindings) argChildren
          | _ => return mk instanceTy #[]
        else
          -- Ctor signature check: all v1 ctor params are required, so arity
          -- is exact (TS2554); each argument checks against its param (TS2345).
          if args.length != info.ctorParams.length then
            emitDiagnostic (.argumentCountMismatch info.ctorParams.length args.length) base.loc
          let mut argChildren : Array TypedExpression := #[]
          for i in [:args.length] do
            let argTyped ← synthJSExpr args[i]!
            argChildren := argChildren.push argTyped
            if let some (_, paramTy) := info.ctorParams[i]? then
              let ok ← isSubtype argTyped.type paramTy
              if !ok then
                emitDiagnostic (.argumentTypeMismatch i argTyped.type paramTy) (exprLoc args[i]!)
          return mk instanceTy argChildren
    return mk .any #[]

  -- Graceful degradation: return any for unhandled expression forms
  | _ => return mk .any #[]

/-- Synthesize the return type of an inline callback (arrow or function expression)
    given the positional types for its parameters. Returns `none` for non-inline
    forms (named refs, identifiers, etc.) so callers can fall back gracefully.
    Only expression-bodied arrows are supported for now; block-bodied callbacks
    return `none` to avoid surfacing spurious diagnostics inside the callback body. -/
partial def synthCallbackBody
    (callback : Expression) (paramTys : List TSType) : TypeCheckM (Option TSType) := do
  match callback with
  | .arrowFunctionExpr _ params (.inl bodyExpr) _ _ _ =>
    let names := callbackParamNames params
    let bindings := names.zip paramTys
    let bodyTyped ← withScope bindings (synthJSExpr bodyExpr)
    return some bodyTyped.type
  | _ => return none
where
  callbackParamNames (params : List FunctionParam) : List String :=
    params.filterMap fun
      | .simple id => some id.name
      | .withDefault id _ => some id.name
      | .rest id => some id.name
      | .pattern _ => none

/-- Synthesize a condition-position expression and require it to be
    boolean — the single entry point for TH0026 condition checks. -/
partial def synthCondition (e : Expression) : TypeCheckM TypedExpression := do
  let typed ← synthJSExpr e
  requireBooleanCondition typed.type (exprLoc e)
  return typed

end

/-- Check that an expression has a type assignable to the expected type -/
def checkExpr (expr : TSExpression) (expected : TSType) : TypeCheckM TypedExpression := do
  let typed ← synthExpr expr (some expected)
  checkAssignable typed.type expected (tsExprLoc expr) (tsExprSourceName expr)
  return typed

end Thales.TypeCheck
