/-
  Thales/Emit/SubsetCheck.lean
  Enforces the Thales-TS v1 subset. Returns TH#### diagnostics for
  any construct outside the subset. Assumes type checking has already
  succeeded; operates on the typed AST.
-/
import Thales.TypeCheck.TSAST
import Thales.TypeCheck.Diagnostic
import Thales.Emit.DirectiveApply
import Thales.Emit.EscapeAnalysis
import Thales.Emit.LoopShape
import Std.Data.HashMap

namespace Thales.Emit

open Thales.AST
open Thales.TypeCheck

/-- Environment for switch exhaustiveness checking.
    aliasEnv maps type alias names to their resolved TSType.
    bindingEnv maps identifier names to their declared TSType.
    voidReturn is true inside a function with no value to return — its
    switch arms may legitimately fall through (`break`), since the unit
    arm the emitter produces is the correct value. -/
structure SwitchEnv where
  aliasEnv   : Std.HashMap String TSType := {}
  bindingEnv : Std.HashMap String TSType := {}
  voidReturn : Bool := false

/-- Method names that mutate their receiver. -/
private def mutatingMethodNames : List String :=
  ["push", "pop", "shift", "unshift", "splice", "sort", "reverse",
   "fill", "copyWithin", "set", "delete", "clear", "add"]

/-- Build a Diagnostic for a ThalesKind at the given optional location. -/
private def mkThalesDiag (kind : ThalesKind) (loc : Option SourceLocation) : Diagnostic :=
  { kind := .thales kind, location := loc }

/-- Mutation-routing context (#24). -/
structure MutCtx where
  /-- Eligibility info for the innermost enclosing function; `none` at
      module level. -/
  info : Option EscapeAnalysis.MutationInfo := none
  /-- Inside a `@throws` function body or under `try`/`catch`. -/
  noMutZone : Bool := false
  /-- Whether eligible mutation is actually emittable here: true only for
      `annotatedFuncDecl` bodies (the do-mode path). Arrow and function
      EXPRESSIONS don't lower through `emitFuncDecl`, so their mutation
      stays rejected in v1 even when the eligibility analysis would allow
      it. -/
  allowEligible : Bool := false

/-- Parameter names of a JS-level function/arrow (typed params live on
    `annotatedFuncDecl` and are handled separately). -/
private def funcParamNames (params : List FunctionParam) : List String :=
  params.filterMap fun
    | .simple id        => some id.name
    | .withDefault id _ => some id.name
    | .rest id          => some id.name
    | .pattern _        => none

/-- Eligibility info for a nested function/arrow body. -/
private def nestedInfo (params : List FunctionParam) (body : Statement)
    : EscapeAnalysis.MutationInfo :=
  EscapeAnalysis.analyze (funcParamNames params) body

/-- Compound operators whose desugared binary op has a working Float
    lowering. Everything except the (deferred, short-circuit) logical
    family: the arithmetic ops lower to Lean operators, and `%`/bitwise/
    shifts route through the JS-semantics runtime helpers (#32). -/
private def emittableMutationOp : AssignmentOperator → Bool
  | .orLogicalAssign | .andLogicalAssign | .nullishAssign => false
  | _ => true

/-- Route a statement-position mutation of identifier `name`.
    Returns the rejection diagnostics; `#[]` means the mutation is allowed.
    `emittable` is false for operators whose lowering isn't implemented. -/
private def routeIdentMutation (ctx : MutCtx) (loc : Option SourceLocation)
    (name : String) (logicalOp : Bool) (emittable : Bool) : Array Diagnostic :=
  match ctx.info with
  | none =>
    -- Module-level mutation stays out of the subset.
    #[mkThalesDiag (.cannotReassignVariable name) loc]
  | some info =>
    if info.consts.contains name then
      -- Reassigning a `const` is tsc's TS2588; no TH code on top.
      #[]
    else if ctx.noMutZone then
      #[mkThalesDiag (.mutationInThrowsContext name) loc]
    else if logicalOp then
      -- `&&=` / `||=` / `??=` are deferred (short-circuit semantics).
      #[mkThalesDiag (.cannotReassignVariable name) loc]
    else if !(info.params.contains name || info.initializedLets.contains name
              || info.uninitializedLets.contains name) then
      -- Not declared in this function: mutation of an outer-scope binding.
      #[mkThalesDiag (.cannotMutateCapturedVariable name) loc]
    else if info.capturedRefs.contains name then
      #[mkThalesDiag (.cannotMutateCapturedVariable name) loc]
    else if info.uninitializedLets.contains name
            || info.narrowTested.contains name
            || !info.doModeLowerable then
      -- Still-rejected forms: `let` without initializer, variables whose
      -- narrowing the emitter relies on, and functions whose body contains
      -- a shape do-mode can't lower — an unlowerable switch, a
      -- `try`/`catch` (#41), or a read of a narrow-tested variable outside
      -- its test (#40). `doModeLowerable` is the same predicate
      -- `emitFuncDecl` gates on; the two must never disagree.
      #[mkThalesDiag (.cannotReassignVariable name) loc]
    else if ctx.allowEligible && emittable then
      -- Eligible mutation (`=`, arithmetic `OP=`, `++`/`--`) in a declared
      -- function body: in subset, lowered to `Id.run do` by the emitter.
      #[]
    else
      #[mkThalesDiag (.cannotReassignVariable name) loc]

mutual

/-- Check an expression for mutation violations. Assignment/update
    expressions reaching this function are in EXPRESSION position
    (statement-position ones are routed by `checkStmt`). -/
partial def checkExpr (ctx : MutCtx) (expr : Expression) : Array Diagnostic :=
  match expr with
  | .assignmentExpr b _ left right =>
    let loc := b.loc
    let targetDiags : Array Diagnostic :=
      match left with
      | .identifier _ _ =>
        #[mkThalesDiag .assignmentInExpressionPosition loc]
      | .memberExpr _ _ _ computed _ =>
        if computed then
          #[mkThalesDiag .cannotAssignArrayElement loc]
        else
          #[mkThalesDiag .cannotAssignObjectProperty loc]
      | _ => #[]
    targetDiags ++ checkExpr ctx right
  | .updateExpr b _ argument _ =>
    let loc := b.loc
    let targetDiags : Array Diagnostic :=
      match argument with
      | .identifier _ _ =>
        #[mkThalesDiag .assignmentInExpressionPosition loc]
      | _ => #[]
    targetDiags ++ checkExpr ctx argument
  | .callExpr b callee arguments _ =>
    let loc := b.loc
    let calleeDiags : Array Diagnostic :=
      match callee with
      | .memberExpr _ obj (.identifier _ propName) false _ =>
        if mutatingMethodNames.elem propName then
          #[mkThalesDiag (.cannotCallMutatingMethod propName) loc]
            ++ checkExpr ctx obj
        else
          checkExpr ctx callee
      | _ => checkExpr ctx callee
    calleeDiags ++ (arguments.foldl (fun acc arg => acc ++ checkExpr ctx arg) #[])
  | .unaryExpr _ _ _ argument =>
    checkExpr ctx argument
  | .binaryExpr _ _ left right =>
    checkExpr ctx left ++ checkExpr ctx right
  | .logicalExpr _ _ left right =>
    checkExpr ctx left ++ checkExpr ctx right
  | .memberExpr _ obj prop _ _ =>
    checkExpr ctx obj ++ checkExpr ctx prop
  | .privateMemberExpr _ obj _ =>
    checkExpr ctx obj
  | .conditionalExpr _ test consequent alternate =>
    checkExpr ctx test ++ checkExpr ctx consequent ++ checkExpr ctx alternate
  | .newExpr _ callee arguments =>
    checkExpr ctx callee ++ (arguments.foldl (fun acc arg => acc ++ checkExpr ctx arg) #[])
  | .chainExpr _ inner =>
    checkExpr ctx inner
  | .sequenceExpr _ exprs =>
    exprs.foldl (fun acc e => acc ++ checkExpr ctx e) #[]
  | .templateLiteral _ _ exprs =>
    exprs.foldl (fun acc e => acc ++ checkExpr ctx e) #[]
  | .taggedTemplate _ tag quasi =>
    checkExpr ctx tag ++ checkExpr ctx quasi
  | .arrayExpr _ elements =>
    elements.foldl (fun acc optE =>
      match optE with
      | some e => acc ++ checkExpr ctx e
      | none => acc) #[]
  | .objectExpr _ props =>
    props.foldl (fun acc p =>
      match p with
      | .regular _ _ v _ _ _ => acc ++ checkExpr ctx v
      | .spread _ arg => acc ++ checkExpr ctx arg) #[]
  -- TH0012: async function expressions — emit diagnostic, still recurse body
  | .functionExpr b _ params body _ async =>
    let ctx' := { ctx with info := some (nestedInfo params body), allowEligible := false }
    (if async then #[mkThalesDiag .asyncNotSupported b.loc] else #[])
      ++ checkStmt ctx' body
  -- TH0012: async arrow functions — emit diagnostic, still recurse body
  | .arrowFunctionExpr b params body _ async _ =>
    let bodyDiags : Array Diagnostic :=
      match body with
      | .inl e =>
        -- Expression-bodied arrow: wrap so escape analysis sees one body.
        let ctx' := { ctx with info := some (nestedInfo params (.exprStmt b e)), allowEligible := false }
        checkExpr ctx' e
      | .inr s =>
        let ctx' := { ctx with info := some (nestedInfo params s), allowEligible := false }
        checkStmt ctx' s
    (if async then #[mkThalesDiag .asyncNotSupported b.loc] else #[])
      ++ bodyDiags
  | .spreadElement _ arg =>
    checkExpr ctx arg
  | .yieldExpr _ arg _ =>
    match arg with
    | some e => checkExpr ctx e
    | none => #[]
  -- TH0012: await expression — emit diagnostic, still recurse argument
  | .awaitExpr b arg =>
    #[mkThalesDiag .asyncNotSupported b.loc] ++ checkExpr ctx arg
  -- TH0030: class expressions — emit diagnostic, optionally TH0031 for extends, do NOT recurse
  | .classExpr b _ superClass _ =>
    let baseDiag := #[mkThalesDiag .classNotSupported b.loc]
    match superClass with
    | some _ => baseDiag ++ #[mkThalesDiag .inheritanceNotSupported b.loc]
    | none => baseDiag
  -- Leaf nodes with no sub-expressions
  | .identifier _ _ => #[]
  | .literal _ _ _ => #[]
  | .thisExpr _ => #[]
  | .super_ _ => #[]
  | .metaProperty _ _ _ => #[]
  | .patternExpr _ _ => #[]

/-- Check a statement for subset violations (mutation + control-flow).
    Statement-position assignment/update to an identifier is routed through
    `routeIdentMutation` (#24); everything else delegates to `checkExpr`. -/
partial def checkStmt (ctx : MutCtx) (stmt : Statement) : Array Diagnostic :=
  match stmt with
  | .emptyStmt _ => #[]
  | .debuggerStmt _ => #[]
  | .exprStmt _ expr =>
    match expr with
    | .assignmentExpr b op (.identifier _ name) right =>
      routeIdentMutation ctx b.loc name op.isLogical (emittableMutationOp op)
        ++ checkExpr ctx right
    | .updateExpr b _ (.identifier _ name) _ =>
      routeIdentMutation ctx b.loc name false true
    | _ => checkExpr ctx expr
  | .blockStmt _ body =>
    body.foldl (fun acc s => acc ++ checkStmt ctx s) #[]
  | .ifStmt _ test consequent alternate =>
    checkExpr ctx test
      ++ checkStmt ctx consequent
      ++ (match alternate with | some s => checkStmt ctx s | none => #[])
  -- TH0010: loop statements.
  -- A loop is ADMITTED (no TH0010, recurse into body) iff:
  --   • ctx.info = some info (we are inside a declared function),
  --   • info.doModeLowerable (no unlowered switch, no try/catch, no
  --     unlowered loop shape, no narrowing-dependent body),
  --   • !ctx.noMutZone (not inside @throws or try/catch),
  --   • ctx.allowEligible (annotated function declaration body), and
  --   • LoopShape.classifyLoop classifies this loop as .forOf or .canonicalFor.
  -- NOT admitted → exactly one TH0010, no recursion into the body.
  --
  -- MutationInfo semantics: info.doModeLowerable reflects EscapeAnalysis's own
  -- loop-shape analysis. A function containing BOTH an admitted-shape loop and a
  -- `while` has hasUnloweredLoopShape=true, so doModeLowerable=false, meaning the
  -- admitted-shape loop also gets TH0010 — required for checker/emitter agreement.
  | .whileStmt b _ _ =>
    -- while is never classifyLoop .forOf or .canonicalFor; always TH0010.
    #[mkThalesDiag .loopNotSupported b.loc]
  | .doWhileStmt b _ _ =>
    -- do-while is never lowerable; always TH0010.
    #[mkThalesDiag .loopNotSupported b.loc]
  | .forInStmt b _ _ _ =>
    -- for-in is never lowerable; always TH0010.
    #[mkThalesDiag .loopNotSupported b.loc]
  | s@(.forStmt b _ _ _ _) =>
    let admitted :=
      match ctx.info with
      | none => false
      | some info =>
        info.doModeLowerable && !ctx.noMutZone && ctx.allowEligible
          && (match LoopShape.classifyLoop s with
              | .canonicalFor _ _ _ => true
              | _ => false)
    if admitted then
      -- The test expression (i < B) and update expression (i++) are part of
      -- the admitted shape: classifyLoop already constrained them to bare
      -- identifier/literal/length forms with no subexpressions worth checking.
      -- Routing i++ through checkExpr would draw .assignmentInExpressionPosition;
      -- the init declaration is not a statement-position child of this function.
      -- So we check only the body.
      match s with
      | .forStmt _ _ _ _ body => checkStmt ctx body
      | _ => #[mkThalesDiag .loopNotSupported b.loc]  -- unreachable
    else
      #[mkThalesDiag .loopNotSupported b.loc]
  | s@(.forOfStmt b _ right body _) =>
    let admitted :=
      match ctx.info with
      | none => false
      | some info =>
        info.doModeLowerable && !ctx.noMutZone && ctx.allowEligible
          && (match LoopShape.classifyLoop s with
              | .forOf _ _ _ _ => true
              | _ => false)
    if admitted then
      -- The loop binder (head declaration) is part of the admitted shape; do not
      -- route it through any statement arm. Check only the RHS expression and body.
      checkExpr ctx right ++ checkStmt ctx body
    else
      #[mkThalesDiag .loopNotSupported b.loc]
  | .breakStmt _ _ => #[]
  | .continueStmt _ _ => #[]
  | .returnStmt _ arg =>
    match arg with
    | some e => checkExpr ctx e
    | none => #[]
  -- TH0063 (non-record throw) is checked syntactically: primitive literals
  -- are rejected. TH0060 (unannotated throw) is no longer emitted here —
  -- Check.lean's throwsAnnotationCheck is the single source of truth.
  | .throwStmt b arg =>
    let nonRecord : Array Diagnostic := match arg with
      | .literal _ (.string _) _
      | .literal _ (.number _) _
      | .literal _ (.boolean _) _
      | .literal _ .null _
      | .literal _ (.bigint _) _ =>
          #[mkThalesDiag .nonRecordThrow b.loc]
      | _ => #[]
    nonRecord ++ checkExpr ctx arg
  -- Untyped `catch (e)` is the standard TS form (tsc rejects `catch (e: E)`
  -- with TS1196); thales infers the catch type from the try-body's Except.
  -- Mutation anywhere under try/catch is TH0007 (#24): the exception path
  -- emits pure Except match-chains, which do-mode cannot thread through.
  | .tryStmt _ block handler _ =>
    let ctx' := { ctx with noMutZone := true }
    let blockDiags := checkStmt ctx' block
    let handlerDiags := match handler with
      | some (CatchClause.mk _ _ handlerBody _) => checkStmt ctx' handlerBody
      | none => #[]
    blockDiags ++ handlerDiags
  | .switchStmt _ discriminant cases =>
    checkExpr ctx discriminant
      ++ cases.foldl (fun acc (SwitchCase.mk _ _ stmts) =>
           stmts.foldl (fun acc2 s => acc2 ++ checkStmt ctx s) acc) #[]
  | .labeledStmt _ _ body =>
    checkStmt ctx body
  | .withStmt _ obj body =>
    checkExpr ctx obj ++ checkStmt ctx body
  | .variableDecl (VariableDeclaration.mk _ decls _) =>
    decls.foldl (fun acc (VariableDeclarator.mk _ _ initOpt _) =>
      match initOpt with
      | some e => acc ++ checkExpr ctx e
      | none => acc) #[]
  -- TH0012: async function declarations — emit diagnostic, still recurse body
  | .functionDecl b _ params body _ async =>
    let ctx' := { ctx with info := some (nestedInfo params body), allowEligible := false }
    (if async then #[mkThalesDiag .asyncNotSupported b.loc] else #[])
      ++ checkStmt ctx' body
  -- TH0030: class declarations — emit diagnostic, optionally TH0031 for extends, do NOT recurse
  | .classDecl b _ superClass _ =>
    let baseDiag := #[mkThalesDiag .classNotSupported b.loc]
    match superClass with
    | some _ => baseDiag ++ #[mkThalesDiag .inheritanceNotSupported b.loc]
    | none => baseDiag

/-- Check class elements for mutation violations. -/
partial def checkClassElements (ctx : MutCtx) (elements : List ClassElement) : Array Diagnostic :=
  elements.foldl (fun acc elem =>
    match elem with
    | .method (MethodDefinition.mk _ key value _ _ _ ..) =>
      acc ++ checkExpr ctx key ++ checkExpr ctx value
    | .field (FieldDefinition.mk _ key valueOpt _ _ ..) =>
      acc ++ checkExpr ctx key ++ (match valueOpt with | some v => checkExpr ctx v | none => #[])
    | .staticBlock _ body =>
      body.foldl (fun acc2 s => acc2 ++ checkStmt ctx s) acc) #[]

end

/-- Check whether a union of TSTypes is discriminated.
    A union is discriminated iff:
    1. Every branch is a TSType.object.
    2. There exists a property name shared by every branch where the type is TSType.stringLit. -/
private def isDiscriminatedUnion (branches : List TSType) : Bool := Id.run do
  if branches.length < 2 then return false
  let perBranch : List (List String) := branches.map fun b =>
    match b with
    | .object members =>
        members.filterMap fun m =>
          match m with
          | .property n (.stringLit _) _optional _readonly => some n
          | _ => none
    | _ => []
  match perBranch with
  | [] => return false
  | first :: rest =>
      let candidates := first.filter (fun n => rest.all (fun r => r.contains n))
      return !candidates.isEmpty

/-- A "literal type" in the Thales subset: a primitive literal (string,
    number, boolean) or an object type whose every property is itself a
    literal type. Recursive: `{ a: 1, b: { c: "x" } }` qualifies. -/
private partial def isLiteralType : TSType → Bool
  | .stringLit _ | .numberLit _ | .booleanLit _ => true
  | .paren inner => isLiteralType inner
  | .object members => members.all fun m =>
      match m with
      | .property _ ty _opt _ro => isLiteralType ty
      | _ => false
  | _ => false

/-- A union of literal types: at least two branches, each one literal. -/
private def isLiteralUnion (branches : List TSType) : Bool :=
  branches.length ≥ 2 && branches.all isLiteralType

/-- Resolve a TSType through type alias references.
    Follows at most one level of .ref to avoid infinite loops in v1. -/
private def resolveType (aliasEnv : Std.HashMap String TSType) : TSType → TSType
  | .ref name _ =>
    match aliasEnv.get? name with
    | some resolved => resolved
    | none => .ref name []
  | .paren inner => resolveType aliasEnv inner
  | other => other

/-- For a discriminated union, find the shared discriminator field and return
    (fieldName, List of expected string-literal values across all branches).
    Returns none if the type is not a clean discriminated union on a single field. -/
private def discriminatorInfo (branches : List TSType) : Option (String × List String) := Id.run do
  if branches.length < 2 then return none
  -- Collect per-branch string-literal property names
  let perBranch : List (List (String × String)) := branches.map fun b =>
    match b with
    | .object members =>
        members.filterMap fun m =>
          match m with
          | .property n (.stringLit s) _optional _readonly => some (n, s)
          | _ => none
    | _ => []
  -- Find shared discriminator field names
  match perBranch with
  | [] => return none
  | first :: rest =>
    let candidateNames := (first.map (·.1)).filter fun n =>
      rest.all fun branch => branch.any (·.1 == n)
    match candidateNames with
    | [] => return none
    | discField :: _ =>
      -- Collect the string-literal value for discField from each branch
      let values : List (Option String) := branches.map fun b =>
        match b with
        | .object members =>
          members.findSome? fun m =>
            match m with
            | .property n (.stringLit s) _ _ => if n == discField then some s else none
            | _ => none
        | _ => none
      -- All branches must have a value for discField
      let allValues := values.filterMap id
      if allValues.length != branches.length then return none
      return some (discField, allValues)

/-- Classify a switch statement (#44). Returns TH0041 when the emitter has
    no lowering for its shape: the scrutinee must be a non-computed
    `ident.field` access whose binding resolves to a discriminated union
    keyed on that field, and every arm (including `default`) must return
    on every control path — the lowering turns arms into match-arm
    expressions with no continuation, so anything else used to be silently
    dropped or miscompiled. Returns TH0040 for a well-shaped but
    non-exhaustive switch; `none` means the switch is lowerable. -/
private def classifySwitch
    (env : SwitchEnv) (loc : Option SourceLocation)
    (discriminant : Expression) (cases : List SwitchCase) : Option Diagnostic :=
  let notLowerable := some (mkThalesDiag .switchNotLowerable loc)
  -- In a value-returning function every arm must return (the lowering
  -- turns arms into match-arm expressions with no continuation); in a
  -- void function a fall-through arm's unit value is already correct.
  if !env.voidReturn
      && cases.any (fun (SwitchCase.mk _ _ ss) => !EscapeAnalysis.stmtsReturn ss) then
    notLowerable
  else
  match discriminant with
  | .memberExpr _ (.identifier _ scrutName) (.identifier _ fieldName) false _ =>
    -- Look up the type of scrutName in the binding environment
    match env.bindingEnv.get? scrutName with
    | none => notLowerable
    | some rawTy =>
      -- Resolve through aliases
      match resolveType env.aliasEnv rawTy with
      | .union branches =>
        -- Get discriminator info
        match discriminatorInfo branches with
        | none => notLowerable
        | some (discField, expectedLiterals) =>
          -- The switch must be on the discriminator field
          if discField != fieldName then notLowerable
          else
            -- A `default` arm makes the switch exhaustive by definition
            -- (the emitter lowers its body as the wildcard arm).
            let hasDefault := cases.any fun (SwitchCase.mk _ test _) => test.isNone
            if hasDefault then none
            else
              -- Collect string-literal case labels
              let coveredLiterals : List String := cases.filterMap fun (SwitchCase.mk _ testOpt _) =>
                match testOpt with
                | some (.literal _ (.string s) _) => some s
                | _ => none
              -- Find missing kinds
              let missing := expectedLiterals.filter fun s => !coveredLiterals.contains s
              if missing.isEmpty then none
              else some (mkThalesDiag (.switchNotExhaustive missing) loc)
      | _ => notLowerable
  | _ => notLowerable

/-- Thread annotated `let`/`const`/`var` declarations into the switch
    checker's binding environment so a switch on an annotated local
    resolves (the emitter threads the same annotations). -/
private def bindSwitchDecls (env : SwitchEnv) : Statement → SwitchEnv
  | .variableDecl (.mk _ decls _) =>
      decls.foldl (fun e d =>
        match d with
        | .mk _ (.identifier id) _ (some ty) =>
            { e with bindingEnv := e.bindingEnv.insert id.name ty }
        | _ => e) env
  | _ => env

/- ── Shadowing check (#45, TH0032) ──
   The emitter flattens bare blocks into their enclosing statement list
   and appends if-continuations into branches, so a block-scoped
   declaration that shadows a name from an enclosing scope of the same
   function captures references meant for the outer binding (accepted
   program, wrong output). tsc allows shadowing; Thales rejects it
   (subset-on-rejection). `var` declarations are exempt — they are
   function-scoped, so re-declaration is the same binding and any
   `var`-vs-`let` conflict is already tsc's TS2451. Nested functions and
   arrows start fresh scope stacks: Lean lambdas shadow correctly, and a
   catch parameter lowers to a real match binder, so neither is flagged. -/

private def setUnion (a b : Std.HashSet String) : Std.HashSet String :=
  b.fold (·.insert ·) a

mutual

/-- Walk one lexical scope's statement list. `outer` holds every name
    bound in enclosing scopes of the same function (params included); the
    fold threads the names declared so far in THIS scope. -/
partial def shadowStmts (outer : Std.HashSet String) (stmts : List Statement)
    : Array Diagnostic :=
  (stmts.foldl (fun (st : Array Diagnostic × Std.HashSet String) s =>
      let (diags, current) := st
      let (d, current') := shadowStmt outer current s
      (diags ++ d, current')) (#[], ({} : Std.HashSet String))).1

/-- Check one statement; returns its diagnostics and the current scope's
    binding set extended with any names this statement declares. -/
partial def shadowStmt (outer current : Std.HashSet String) (stmt : Statement)
    : Array Diagnostic × Std.HashSet String :=
  let enter := setUnion outer current
  match stmt with
  | .variableDecl (.mk _ decls kind) =>
      decls.foldl (fun (st : Array Diagnostic × Std.HashSet String) d =>
        let (diags, cur) := st
        let (.mk db pat init _) := d
        let initDiags := match init with
          | some e => shadowExpr e
          | none => #[]
        match pat with
        | .identifier id =>
            let shadowDiag :=
              if kind != .var && outer.contains id.name then
                #[mkThalesDiag (.shadowingNotSupported id.name) db.loc]
              else #[]
            (diags ++ initDiags ++ shadowDiag, cur.insert id.name)
        | _ => (diags ++ initDiags, cur)) (#[], current)
  | .blockStmt _ body => (shadowStmts enter body, current)
  | .ifStmt _ t c a =>
      (shadowExpr t
        ++ shadowStmts enter [c]
        ++ (match a with | some s => shadowStmts enter [s] | none => #[]), current)
  | .switchStmt _ d cases =>
      -- the entire switch body is ONE block scope shared by all arms
      let testDiags := cases.foldl (fun acc c =>
        let (SwitchCase.mk _ t _) := c
        acc ++ (match t with | some e => shadowExpr e | none => #[])) (shadowExpr d)
      let armStmts := cases.flatMap fun (SwitchCase.mk _ _ ss) => ss
      (testDiags ++ shadowStmts enter armStmts, current)
  | .tryStmt _ b h f =>
      let hDiags := match h with
        | some (CatchClause.mk _ paramOpt hb _) =>
            -- the catch param binds (as a real match binder) in the
            -- handler's enclosing set
            let enter' := match paramOpt with
              | some (.identifier id) => enter.insert id.name
              | _ => enter
            shadowStmts enter' [hb]
        | none => #[]
      (shadowStmts enter [b]
        ++ hDiags
        ++ (match f with | some s => shadowStmts enter [s] | none => #[]), current)
  | .forStmt _ init t u b =>
      let initDiags := match init with
        | some (.inl e) => shadowExpr e
        | some (.inr vd) => (shadowStmt enter {} (.variableDecl vd)).1
        | none => #[]
      (initDiags
        ++ (match t with | some e => shadowExpr e | none => #[])
        ++ (match u with | some e => shadowExpr e | none => #[])
        ++ shadowStmts enter [b], current)
  | .forInStmt _ left r b | .forOfStmt _ left r b _ =>
      let leftDiags := match left with
        | .inl e => shadowExpr e
        | .inr vd => (shadowStmt enter {} (.variableDecl vd)).1
      (leftDiags ++ shadowExpr r ++ shadowStmts enter [b], current)
  | .whileStmt _ t b => (shadowExpr t ++ shadowStmts enter [b], current)
  | .doWhileStmt _ b t => (shadowStmts enter [b] ++ shadowExpr t, current)
  | .exprStmt _ e | .throwStmt _ e => (shadowExpr e, current)
  | .returnStmt _ a =>
      ((match a with | some e => shadowExpr e | none => #[]), current)
  | .functionDecl _ _ params body _ _ =>
      -- nested function: fresh scope stack seeded with its params
      (shadowFunc (funcParamNames params) body, current)
  | .labeledStmt _ _ b | .withStmt _ _ b => (shadowStmts enter [b], current)
  | _ => (#[], current)

/-- Find nested function/arrow bodies inside an expression and shadow-check
    each with a fresh scope stack. -/
partial def shadowExpr : Expression → Array Diagnostic
  | .functionExpr _ _ params body _ _ => shadowFunc (funcParamNames params) body
  | .arrowFunctionExpr _ params body _ _ _ =>
      (match body with
        | .inl e => shadowExpr e
        | .inr s => shadowFunc (funcParamNames params) s)
  | .unaryExpr _ _ _ a | .updateExpr _ _ a _ | .spreadElement _ a
  | .awaitExpr _ a | .chainExpr _ a | .privateMemberExpr _ a _ => shadowExpr a
  | .binaryExpr _ _ l r | .assignmentExpr _ _ l r | .logicalExpr _ _ l r
  | .taggedTemplate _ l r => shadowExpr l ++ shadowExpr r
  | .memberExpr _ o p _ _ => shadowExpr o ++ shadowExpr p
  | .conditionalExpr _ t c a => shadowExpr t ++ shadowExpr c ++ shadowExpr a
  | .callExpr _ f args _ | .newExpr _ f args =>
      args.foldl (fun acc a => acc ++ shadowExpr a) (shadowExpr f)
  | .arrayExpr _ els =>
      els.foldl (fun acc oe => match oe with
        | some e => acc ++ shadowExpr e
        | none => acc) #[]
  | .objectExpr _ props =>
      props.foldl (fun acc p => match p with
        | .regular _ k v _ _ _ => acc ++ shadowExpr k ++ shadowExpr v
        | .spread _ a => acc ++ shadowExpr a) #[]
  | .sequenceExpr _ es | .templateLiteral _ _ es =>
      es.foldl (fun acc e => acc ++ shadowExpr e) #[]
  | .yieldExpr _ a _ =>
      (match a with | some e => shadowExpr e | none => #[])
  | _ => #[]

/-- Shadow-check a function: its parameters form the outermost scope. -/
partial def shadowFunc (paramNames : List String) (body : Statement)
    : Array Diagnostic :=
  shadowStmts (paramNames.foldl (·.insert ·) ({} : Std.HashSet String)) [body]

end

/-- Walk a statement body checking for switch exhaustiveness violations.
    Uses the provided SwitchEnv for identifier lookups. -/
partial def checkSwitchStmt (env : SwitchEnv) (stmt : Statement) : Array Diagnostic :=
  match stmt with
  | .blockStmt _ body =>
    -- Thread annotated declarations through the statement list so later
    -- switches on annotated locals resolve.
    (body.foldl (fun (st : Array Diagnostic × SwitchEnv) s =>
      let (acc, env) := st
      (acc ++ checkSwitchStmt env s, bindSwitchDecls env s)) (#[], env)).1
  | .ifStmt _ _ consequent alternate =>
    checkSwitchStmt env consequent
      ++ (match alternate with | some s => checkSwitchStmt env s | none => #[])
  | .switchStmt b discriminant cases =>
    let switchDiag : Array Diagnostic :=
      match classifySwitch env b.loc discriminant cases with
      | some d => #[d]
      | none => #[]
    -- Also recurse into case bodies for nested switches
    let caseDiags := cases.foldl (fun acc (SwitchCase.mk _ _ stmts) =>
      stmts.foldl (fun acc2 s => acc2 ++ checkSwitchStmt env s) acc) #[]
    switchDiag ++ caseDiags
  | .returnStmt _ _ => #[]
  | .throwStmt _ _ => #[]
  | .tryStmt _ block handler finalizer =>
    checkSwitchStmt env block
      ++ (match handler with
          | some (CatchClause.mk _ _ body _) => checkSwitchStmt env body
          | none => #[])
      ++ (match finalizer with | some s => checkSwitchStmt env s | none => #[])
  | .labeledStmt _ _ body => checkSwitchStmt env body
  | .withStmt _ _ body => checkSwitchStmt env body
  | .functionDecl _ _ _ body _ _ =>
    -- Function declarations create a new scope; bindings don't leak in or out.
    checkSwitchStmt { aliasEnv := env.aliasEnv, bindingEnv := {} } body
  | _ => #[]

/-- Walk a TSType and collect TH0020-TH0025 diagnostics. `defaultLoc`
    attaches a source location (typically the enclosing declaration's
    `NodeBase.loc`) to every diagnostic produced — type nodes don't carry
    locations themselves, so we thread one in from the statement. -/
partial def checkType (defaultLoc : Option SourceLocation) (ty : TSType) : Array Diagnostic :=
  Id.run do
    let mut diags : Array Diagnostic := #[]
    match ty with
    | .any => diags := diags.push (mkThalesDiag .anyNotPermitted defaultLoc)
    | .unknown => diags := diags.push (mkThalesDiag .unknownNotPermitted defaultLoc)
    | .null_ => diags := diags.push (mkThalesDiag .nullUndefinedNotSupported defaultLoc)
    | .undefined => diags := diags.push (mkThalesDiag .nullUndefinedNotSupported defaultLoc)
    | .intersection _ =>
        diags := diags.push (mkThalesDiag .intersectionNotSupported defaultLoc)
        -- don't descend into intersection members (already forbidden)
    | .conditional _ _ _ _ =>
        diags := diags.push (mkThalesDiag .typeLevelProgrammingNotSupported defaultLoc)
    | .mapped _ _ _ _ _ =>
        diags := diags.push (mkThalesDiag .typeLevelProgrammingNotSupported defaultLoc)
    | .option inner =>
        -- T | null / T | undefined: accepted, check inner type only
        diags := diags ++ checkType defaultLoc inner
    | .union members =>
        -- A nullable union (T | null or T | undefined) is accepted; emit as Option T
        match normalizeNullableUnion members with
        | some (.option inner) =>
            diags := diags ++ checkType defaultLoc inner
        | _ =>
            if !isDiscriminatedUnion members && !isLiteralUnion members then
              diags := diags.push (mkThalesDiag .unionMustBeDiscriminated defaultLoc)
            for m in members do
              diags := diags ++ checkType defaultLoc m
    | .array elem => diags := diags ++ checkType defaultLoc elem
    | .tuple elems =>
        for e in elems do diags := diags ++ checkType defaultLoc e
    | .function params ret =>
        for (.mk _ pty _ _) in params do diags := diags ++ checkType defaultLoc pty
        diags := diags ++ checkType defaultLoc ret
    | .object members =>
        for m in members do
          match m with
          | .property _ pty _ _ => diags := diags ++ checkType defaultLoc pty
          | .method _ params ret _ =>
              for (.mk _ pty _ _) in params do diags := diags ++ checkType defaultLoc pty
              diags := diags ++ checkType defaultLoc ret
          | .indexSignature _ _keyTy valTy _ => diags := diags ++ checkType defaultLoc valTy
    | .paren inner => diags := diags ++ checkType defaultLoc inner
    | _ => pure ()
    return diags

/-- Extract the TSType from a TypeAnnotation and check it. -/
private def checkAnn (defaultLoc : Option SourceLocation) (ann : Option TypeAnnotation) : Array Diagnostic :=
  match ann with
  | none => #[]
  | some a => checkType defaultLoc a.type

/-- Build a SwitchEnv from a program body: collect type aliases. -/
private def buildAliasEnv (body : List TSStatement) : Std.HashMap String TSType :=
  body.foldl (fun env ts =>
    match ts with
    | .typeAliasDecl _ name _ ty => env.insert name ty
    | .declareStmt _ (.typeAliasDecl _ name _ ty) => env.insert name ty
    | _ => env) {}

/-- Build a binding environment from annotated function parameters. -/
private def buildParamEnv
    (params : List (String × Option TypeAnnotation × Bool × Bool))
    : Std.HashMap String TSType :=
  params.foldl (fun env (name, annOpt, _, _) =>
    match annOpt with
    | some ann => env.insert name ann.type
    | none => env) {}

/-- Check a TS-level statement for mutation violations. -/
def checkTSStmt (ts : TSStatement) : Array Diagnostic :=
  match ts with
  | .js s => checkStmt {} s ++ shadowStmts {} [s]
  | .annotatedVarDecl b _ _ typeAnn initOpt =>
    checkAnn b.loc typeAnn
      ++ (match initOpt with
          | some e => checkExpr {} e ++ shadowExpr e
          | none => #[])
  -- TH0012: async annotated function declarations — emit diagnostic, still recurse body.
  -- TH0060 is no longer SubsetCheck's responsibility, so no suppression filter is needed.
  | .annotatedFuncDecl b _ _ params returnType body _ async throwsAnn _ =>
    let ctx : MutCtx :=
      { info := some (EscapeAnalysis.analyze (params.map (·.1)) body),
        noMutZone := throwsAnn != .absent,
        allowEligible := true }
    let paramTypeDiags := params.foldl (fun acc (_, ann, _, _) =>
      acc ++ checkAnn b.loc ann) #[]
    let bodyDiags := checkStmt ctx body
    (if async then #[mkThalesDiag .asyncNotSupported b.loc] else #[])
      ++ paramTypeDiags
      ++ checkAnn b.loc returnType
      ++ bodyDiags
      ++ shadowFunc (params.map (·.1)) body
  | .interfaceDecl b _ _ _ members =>
    members.foldl (fun acc m =>
      match m with
      | .property _ ty _ _ => acc ++ checkType b.loc ty
      | .method _ params ret _ =>
          let pd := params.foldl (fun a (.mk _ pty _ _) => a ++ checkType b.loc pty) #[]
          acc ++ pd ++ checkType b.loc ret) #[]
  | .typeAliasDecl b _ _ ty => checkType b.loc ty
  | .enumDecl _ _ _ _ => #[]
  | .declareStmt _ inner => checkTSStmt inner
  | .importDecl _ _ _ => #[]

/-- Check a TS-level statement for switch lowerability and exhaustiveness
    (TH0041/TH0040). Requires a SwitchEnv with type alias and binding
    information. -/
def checkTSStmtSwitch (aliasEnv : Std.HashMap String TSType) (ts : TSStatement)
    : Array Diagnostic :=
  match ts with
  | .annotatedFuncDecl _ _ _ params returnType body _ _ _ _ =>
    let bindingEnv := buildParamEnv params
    let voidReturn := match returnType with
      | none => true
      | some ann => ann.type == .void_
    let env : SwitchEnv := { aliasEnv, bindingEnv, voidReturn }
    checkSwitchStmt env body
  | .js s => checkSwitchStmt { aliasEnv, bindingEnv := {} } s
  | _ => #[]

/-- Walk a TSProgram and return all Thales-subset violations (raw,
    without directive post-processing). -/
def subsetCheckRaw (prog : TSProgram) : Array Diagnostic :=
  let aliasEnv := buildAliasEnv prog.body
  prog.body.foldl (fun acc ts =>
    acc ++ checkTSStmt ts ++ checkTSStmtSwitch aliasEnv ts) #[]

/-- Subset check with `@thales-expect-error` directives applied.
    Suppresses TH diagnostics on lines covered by matching directives and
    emits TH9000/TH9001/TH9003 as appropriate. -/
def subsetCheck (prog : TSProgram) : Array Diagnostic :=
  let raw := subsetCheckRaw prog
  DirectiveApply.apply raw prog.expectErrorDirectives

/-- Subset check without directive application — the raw TH set.
    Used by the harness (`--ignore-expect-error`) and for the emit gate. -/
def subsetCheckIgnoringDirectives (prog : TSProgram) : Array Diagnostic :=
  subsetCheckRaw prog

end Thales.Emit
