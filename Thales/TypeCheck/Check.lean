import Thales.TypeCheck.TSType
import Thales.TypeCheck.TSAST
import Thales.TypeCheck.Context
import Thales.TypeCheck.Synth
import Thales.TypeCheck.Diagnostic
import Thales.TypeCheck.Builtins
import Thales.TypeCheck.Generic
import Thales.TypeCheck.TypeSubstitution
import Thales.TypeCheck.Assignability
import Thales.TypeCheck.Narrowing

namespace Thales.TypeCheck

open Thales.AST

private def exprLoc : Expression → Option SourceLocation
  | .identifier base _ => base.loc
  | .literal base _ _ => base.loc
  | .callExpr base _ _ _ => base.loc
  | .binaryExpr base _ _ _ => base.loc
  | .memberExpr base _ _ _ _ => base.loc
  | .assignmentExpr base _ _ _ => base.loc
  | _ => none

/-- Collect all variable names declared in a JS statement with their declared types.
    Uses type annotation if present, otherwise falls back to `any`. -/
private def collectDeclaredBindings : Statement → List (String × TSType)
  | .variableDecl (.mk _ declarators _) =>
    declarators.filterMap fun (.mk _ pat _ typeAnn) =>
      match pat with
      | .identifier id => some (id.name, typeAnn.getD .any)
      | _ => none
  | .blockStmt _ stmts => stmts.flatMap collectDeclaredBindings
  | _ => []

/-- Collect all `var`-declared names from a JS statement, recursing into
    blocks/if/for/while/try but stopping at function boundaries. -/
private partial def collectHoistedVarsJS : Statement → List String
  | .variableDecl (.mk _ declarators .var) =>
    declarators.filterMap fun (.mk _ pat _ _) =>
      match pat with
      | .identifier id => some id.name
      | _ => none
  | .blockStmt _ body =>
    body.flatMap collectHoistedVarsJS
  | .ifStmt _ _ consequent alternate =>
    collectHoistedVarsJS consequent ++
    match alternate with
    | some alt => collectHoistedVarsJS alt
    | none => []
  | .whileStmt _ _ body =>
    collectHoistedVarsJS body
  | .doWhileStmt _ body _ =>
    collectHoistedVarsJS body
  | .forStmt _ init _ _ body =>
    let initVars := match init with
      | some (.inr (.mk _ declarators .var)) =>
        declarators.filterMap fun (.mk _ pat _ _) =>
          match pat with
          | .identifier id => some id.name
          | _ => none
      | _ => []
    initVars ++ collectHoistedVarsJS body
  | .forInStmt _ left _ body =>
    let leftVars := match left with
      | .inr (.mk _ declarators .var) =>
        declarators.filterMap fun (.mk _ pat _ _) =>
          match pat with
          | .identifier id => some id.name
          | _ => none
      | _ => []
    leftVars ++ collectHoistedVarsJS body
  | .forOfStmt _ left _ body _ =>
    let leftVars := match left with
      | .inr (.mk _ declarators .var) =>
        declarators.filterMap fun (.mk _ pat _ _) =>
          match pat with
          | .identifier id => some id.name
          | _ => none
      | _ => []
    leftVars ++ collectHoistedVarsJS body
  | .tryStmt _ block handler finalizer =>
    collectHoistedVarsJS block ++
    (match handler with
    | some (.mk _ _ handlerBody _) => collectHoistedVarsJS handlerBody
    | none => []) ++
    (match finalizer with
    | some fin => collectHoistedVarsJS fin
    | none => [])
  | .switchStmt _ _ cases =>
    cases.flatMap fun (.mk _ _ consequent) =>
      consequent.flatMap collectHoistedVarsJS
  | .labeledStmt _ _ body =>
    collectHoistedVarsJS body
  -- Stop at function boundaries — var does not cross these
  | .functionDecl .. => []
  -- All other statements: no var declarations to collect
  | _ => []

/-- Collect all `var`-declared names in a TS statement list, recursing into
    blocks/if/for/while/try but stopping at function boundaries.
    Works on both TS and JS statement layers. -/
private def collectHoistedVars : List TSStatement → List String
  | [] => []
  | stmt :: rest =>
    let names := match stmt with
      -- TS annotated var declaration
      | .annotatedVarDecl _ .var name _ _ => [name]
      | .annotatedVarDecl _ _ _ _ _ => []  -- let/const: don't hoist
      -- JS statement: delegate to JS-level collector
      | .js s => collectHoistedVarsJS s
      -- All other TS statements: no var declarations to collect
      | _ => []
    names ++ collectHoistedVars rest

/-- Collect variable names that are assigned in a statement (shallow scan for loop widening) -/
private partial def collectAssignedVars : Statement → List String
  | .exprStmt _ (.assignmentExpr _ _ (.identifier _ name) _) => [name]
  | .blockStmt _ body => body.flatMap collectAssignedVars
  | .ifStmt _ _ consequent alternate =>
    collectAssignedVars consequent ++
    (match alternate with | some alt => collectAssignedVars alt | none => [])
  | .whileStmt _ _ body => collectAssignedVars body
  | .doWhileStmt _ body _ => collectAssignedVars body
  | .forStmt _ _ _ _ body => collectAssignedVars body
  | .forInStmt _ _ _ body => collectAssignedVars body
  | .forOfStmt _ _ _ body _ => collectAssignedVars body
  | .switchStmt _ _ cases =>
    cases.flatMap fun (.mk _ _ consequent) => consequent.flatMap collectAssignedVars
  | .tryStmt _ block handler finalizer =>
    collectAssignedVars block ++
    (match handler with | some (.mk _ _ handlerBody _) => collectAssignedVars handlerBody | none => []) ++
    (match finalizer with | some fin => collectAssignedVars fin | none => [])
  | _ => []

/-- Widen variables that are assigned in a loop body back to their declared types.
    Returns bindings diffs for variables whose flow type differs from declared type. -/
private def widenAssignedVars (assignedNames : List String) : TypeCheckM (List (String × TSType)) := do
  let ctx ← read
  let mut widened : List (String × TSType) := []
  for name in assignedNames.eraseDups do
    match ctx.declaredTypes[name]? with
    | some declTy =>
      match ctx.bindings[name]? with
      | some flowTy => if flowTy != declTy then widened := widened ++ [(name, declTy)]
      | none => pure ()
    | none => pure ()
  return widened

/-- Build an instance TSType from a class body, inheriting members from an optional superclass -/
private def buildClassInstanceType (superClass : Option Expression) (body : List ClassElement) : TypeCheckM TSType := do
  -- Inherit members from superclass if known
  let mut instanceMembers : List TSObjectMember := []
  match superClass with
  | some (.identifier _ superName) =>
    let ctx ← read
    if let some (.object parentMembers) := ctx.classes[superName]? then
      instanceMembers := parentMembers
  | _ => pure ()
  -- Collect instance fields and methods from the class body
  for element in body do
    match element with
    | .field (.mk _ key _value _computed static_ _) =>
      if !static_ then
        if let .identifier _ fieldName := key then
          instanceMembers := instanceMembers ++ [.property fieldName .any false false]
    | .method (.mk _ key _value kind _computed static_ _) =>
      if !static_ then
        if let .identifier _ methodName := key then
          match kind with
          | .method =>
            instanceMembers := instanceMembers ++ [.method methodName [] .any false]
          | _ => pure ()  -- constructor/getter/setter: skip for now
    | _ => pure ()
  return .object instanceMembers

/-- Resolve type alias refs in bindings so narrowing sees concrete union/object types.
    Only resolves bindings for the variables mentioned in the guard. -/
private def resolveBindingsForNarrowing (guard : Narrowing.Guard) (bindings : Std.HashMap String TSType) : TypeCheckM (Std.HashMap String TSType) := do
  let vars := Narrowing.guardVarNames guard
  vars.foldlM (fun acc varName =>
    match acc[varName]? with
    | some ty => do
      let resolved ← resolveTypeGeneric ty
      return acc.insert varName resolved
    | none => return acc
  ) bindings

mutual

/-- Check a TS statement, returning a continuation that processes remaining statements
    with any new bindings in scope. -/
partial def checkStatement (stmt : TSStatement) (rest : List TSStatement) : TypeCheckM Unit := do
  match stmt with
  | .js s =>
    -- Special handling for class declarations (need scope threading)
    match s with
    | .classDecl _base id superClass body =>
      let baseInstanceTy ← buildClassInstanceType superClass body
      -- Check if there's a companion interface with the same name (for generic class support).
      -- If so, build the instance type from the interface members (with typeVars) instead.
      let instanceTy ← do
        let ctx ← read
        if let some ifaceDef := ctx.interfaces[id.name]? then
          if ifaceDef.typeParams.length > 0 then
            -- Allocate fresh typeVars for each type param
            let (typeVarIds, _) ← allocTypeVars ifaceDef.typeParams
            -- Build instance type from interface members, replacing name-based refs with typeVars
            let members := ifaceDef.members.map fun member =>
              let replaceRefs := fun (ty : TSType) =>
                typeVarIds.foldl (fun t (id_, param) => replaceRefWithTypeVar t param.name id_) ty
              match member with
              | .property n t o r => TSObjectMember.property n (replaceRefs t) o r
              | .method n ps ret o =>
                TSObjectMember.method n
                  (ps.map fun (.mk pn pt po pr) => TSParamType.mk pn (replaceRefs pt) po pr)
                  (replaceRefs ret) o
            pure (.object members)
          else
            pure baseInstanceTy
        else
          pure baseInstanceTy
      -- Check method bodies in their own scopes (with params bound as `any`)
      for element in body do
        match element with
        | .method (.mk _ _ value _ _ _ _) =>
          if let .functionExpr _ _ params methodBody _ _ := value then
            let paramBindings := params.map fun
              | .simple { name, .. } | .withDefault { name, .. } _ | .rest { name, .. } => (name, TSType.any)
              | .pattern _ => ("_", TSType.any)
            let hoisted := collectHoistedVars [.js methodBody]
            let paramNames := paramBindings.map (·.1)
            let hoistedBindings := hoisted.filter (!paramNames.contains ·)
              |>.map fun n => (n, TSType.any)
            withFunctionScope (paramBindings ++ hoistedBindings) none (checkJSStatementRaw methodBody)
        | _ => pure ()
      withClass id.name instanceTy (checkStatements rest)
    | _ =>
      checkJSStatementRaw s
      checkStatements rest
  | .annotatedVarDecl _base _kind name typeAnn init =>
    -- Determine the variable's type
    let varTy ← match typeAnn, init with
      | some ann, some initExpr =>
        -- Both annotation and initializer: check initializer against annotation
        let annTy := ann.type
        let initTyped ← synthExpr (.js initExpr)
        let srcName := tsExprSourceName (.js initExpr)
        checkAssignable initTyped.type annTy (exprLoc initExpr) srcName
        pure annTy
      | some ann, none =>
        -- Annotation only
        pure ann.type
      | none, some initExpr =>
        -- Initializer only: infer type
        let initTyped ← synthExpr (.js initExpr)
        pure initTyped.type
      | none, none =>
        -- Neither: implicitly any
        pure .any
    -- Definite assignment tracking
    match _kind with
    | .let_ | .const =>
      match init with
      | some _ => markAssigned name
      | none => requireAssignmentCheck name
    | .var => markAssigned name  -- var hoisted as undefined, always "assigned"
    -- Process remaining statements with the new binding in scope
    withScope [(name, varTy)] (checkStatements rest)
  | .annotatedFuncDecl _base name typeParams params returnType body _ _ _ _ =>
    -- Allocate type variables for generic type params (constraints are embedded in typeVars)
    let (typeVarIds, _) ← allocTypeVars typeParams
    -- Build name→(id, constraint) mapping for replacing refs with typeVars
    let refToVar := typeVarIds.map fun (id, param) => (param.name, id, param.constraint)
    -- Build param bindings with type param refs replaced by typeVars (constraints propagated)
    let paramBindings := params.map fun (pname, typeAnn, opt, rest_) =>
      let ty := match typeAnn with
        | some ann =>
          refToVar.foldl (fun t (refName, varId, con) => replaceRefWithTypeVar t refName varId con) ann.type
        | none => .any
      (pname, ty, opt, rest_)
    -- Determine return type (with type param refs replaced by typeVars)
    let retTy := match returnType with
      | some ann =>
        some (refToVar.foldl (fun t (refName, varId, con) => replaceRefWithTypeVar t refName varId con) ann.type)
      | none => none
    -- Register the function binding (with optional/rest info preserved)
    let funcTy := TSType.function
      (paramBindings.map fun (pname, ty, opt, rest_) => .mk pname ty opt rest_)
      (retTy.getD .any)
    -- Save DA state before entering function scope
    let savedDA ← saveAssignmentState
    let savedChecks := (← get).needsAssignmentCheck
    modify fun s => { s with assignedVars := {}, needsAssignmentCheck := {} }
    -- Mark all parameters as assigned (params are always initialized)
    for (pname, _, _, _) in paramBindings do
      markAssigned pname
    -- Check function body in its own scope (only need name/type for scope)
    let scopeBindings := paramBindings.map fun (pname, ty, _, _) => (pname, ty)
    -- Pre-seed hoisted var declarations (function-scoped)
    let hoisted := collectHoistedVars [.js body]
    let paramNames := scopeBindings.map (·.1)
    let hoistedBindings := hoisted.filter (!paramNames.contains ·)
      |>.map fun n => (n, TSType.any)
    -- Include the function name in its own scope to support direct recursion
    withFunctionScope (scopeBindings ++ hoistedBindings ++ [(name, funcTy)]) retTy (checkJSStatementRaw body)
    -- Restore outer DA state
    restoreAssignmentState savedDA
    modify fun s => { s with needsAssignmentCheck := savedChecks }
    -- Process remaining statements with function in scope
    withScope [(name, funcTy)] (checkStatements rest)
  | .interfaceDecl _base name typeParams _extends members =>
    withInterface name { typeParams, members } (checkStatements rest)
  | .typeAliasDecl _base name typeParams ty =>
    withTypeAlias name { typeParams, body := ty } (checkStatements rest)
  | .enumDecl _base name members _isConst =>
    -- Register enum as an object type with member properties.
    -- Each member's type is the enum's own ref type so that 'Color.Red : Color'.
    let enumRef := TSType.ref name []
    let memberTypes := members.map fun m =>
      TSObjectMember.property m.name enumRef false true
    let enumTy := TSType.object memberTypes
    withEnum name enumTy (checkStatements rest)
  | .declareStmt _base inner =>
    -- Register declarations without checking bodies
    match inner with
    | .annotatedFuncDecl _ fname _ params returnType _ _ _ _ _ =>
      let paramTypes := params.map fun (pname, typeAnn, opt, rest_) =>
        let ty := match typeAnn with | some ann => ann.type | none => .any
        TSParamType.mk pname ty opt rest_
      let retTy := match returnType with | some ann => ann.type | none => .any
      let funcTy := TSType.function paramTypes retTy
      withScope [(fname, funcTy)] (checkStatements rest)
    | .annotatedVarDecl _ _ vname typeAnn _ =>
      let ty := match typeAnn with | some ann => ann.type | none => .any
      withScope [(vname, ty)] (checkStatements rest)
    | _ => checkStatements rest
  | .importDecl _ source _ =>
    -- Special-case @thales/prelude: inject the in-memory shim bindings.
    -- For all other imports, just continue (no filesystem resolution).
    if source == "@thales/prelude" then
      -- Type aliases: Integer/Natural/Byte/Bit are refinement-tagged variants of `number`.
      let aliasOf (ty : TSType) := { typeParams := [], body := ty : TypeAliasDef }
      let intTy : TSType := .refinement .integer
      let natTy : TSType := .refinement .natural
      let byteTy : TSType := .refinement .byte
      let bitTy : TSType := .refinement .bit
      -- Value types for is-predicates: (x: number) => boolean
      let numToBoolean := TSType.function [TSParamType.mk "x" .number] .boolean
      -- Value types for as-constructors: (x: number) => <refinement>
      let asInt := TSType.function [TSParamType.mk "x" .number] intTy
      let asNat := TSType.function [TSParamType.mk "x" .number] natTy
      let asByte := TSType.function [TSParamType.mk "x" .number] byteTy
      let asBit := TSType.function [TSParamType.mk "x" .number] bitTy
      let preludeValues : List (String × TSType) := [
        ("isInteger", numToBoolean), ("isNatural", numToBoolean),
        ("isByte",    numToBoolean), ("isBit",     numToBoolean),
        ("asInteger", asInt),        ("asNatural",  asNat),
        ("asByte",    asByte),       ("asBit",      asBit)
      ]
      withTypeAlias "Integer" (aliasOf intTy)
        (withTypeAlias "Natural" (aliasOf natTy)
          (withTypeAlias "Byte" (aliasOf byteTy)
            (withTypeAlias "Bit" (aliasOf bitTy)
              (withScope preludeValues (checkStatements rest)))))
    else
      checkStatements rest

/-- Check a JS statement without processing continuation -/
partial def checkJSStatementRaw (stmt : Statement) : TypeCheckM Unit := do
  match stmt with
  | .exprStmt _ expr =>
    let _ ← synthJSExpr expr
  | .returnStmt _base arg =>
    let ctx ← read
    match ctx.returnType, arg with
    | some expected, some expr =>
      let actualTyped ← synthJSExpr expr
      checkAssignable actualTyped.type expected (exprLoc expr) (exprSourceName expr)
    | some expected, none =>
      -- Return without value in a function that expects a return type
      match expected with
      | .void_ | .any | .undefined => pure ()
      | _ => pure ()  -- Could emit noReturnValue, but tricky to get right
    | none, _ => pure ()  -- No return type annotation, anything goes
  | .blockStmt _ body =>
    checkJSStatements body
  | .ifStmt _ test consequent alternate =>
    let _ ← synthJSExpr test
    let ctx ← read
    let preBranchDA ← saveAssignmentState
    match Narrowing.extractGuard test with
    | some guard =>
      let resolvedBindings ← resolveBindingsForNarrowing guard ctx.bindings
      let thenBindings := Narrowing.applyGuard guard resolvedBindings
      let elseBindings := Narrowing.applyNegatedGuard guard resolvedBindings
      withScope (Narrowing.bindingsDiff thenBindings ctx.bindings) (checkJSStatementRaw consequent)
      let thenDA ← saveAssignmentState
      restoreAssignmentState preBranchDA
      match alternate with
      | some alt =>
        withScope (Narrowing.bindingsDiff elseBindings ctx.bindings) (checkJSStatementRaw alt)
        let elseDA ← saveAssignmentState
        restoreAssignmentState (intersectAssigned thenDA elseDA)
      | none =>
        restoreAssignmentState (intersectAssigned thenDA preBranchDA)
    | none =>
      checkJSStatementRaw consequent
      let thenDA ← saveAssignmentState
      restoreAssignmentState preBranchDA
      match alternate with
      | some alt =>
        checkJSStatementRaw alt
        let elseDA ← saveAssignmentState
        restoreAssignmentState (intersectAssigned thenDA elseDA)
      | none =>
        restoreAssignmentState (intersectAssigned thenDA preBranchDA)
  | .whileStmt _ test body =>
    let _ ← synthJSExpr test
    let preLoopDA ← saveAssignmentState
    -- Widen variables assigned in the loop body back to declared types
    let assignedInLoop := collectAssignedVars body
    let widened ← widenAssignedVars assignedInLoop
    let ctx ← read
    match Narrowing.extractGuard test with
    | some guard =>
      let resolvedBindings ← resolveBindingsForNarrowing guard ctx.bindings
      let narrowed := Narrowing.applyGuard guard resolvedBindings
      withScope (widened ++ Narrowing.bindingsDiff narrowed ctx.bindings) (checkJSStatementRaw body)
    | none =>
      withScope widened (checkJSStatementRaw body)
    restoreAssignmentState preLoopDA
  | .doWhileStmt _ body test =>
    let preLoopDA ← saveAssignmentState
    let assignedInLoop := collectAssignedVars body
    let widened ← widenAssignedVars assignedInLoop
    withScope widened (checkJSStatementRaw body)
    let _ ← synthJSExpr test
    restoreAssignmentState preLoopDA
  | .forStmt _ init test update body =>
    match init with
    | some (.inl expr) => let _ ← synthJSExpr expr
    | some (.inr _varDecl) => pure ()
    | none => pure ()
    match test with
    | some expr => let _ ← synthJSExpr expr
    | none => pure ()
    let preLoopDA ← saveAssignmentState
    let assignedInLoop := collectAssignedVars body
    let widened ← widenAssignedVars assignedInLoop
    match update with
    | some expr => let _ ← synthJSExpr expr
    | none => pure ()
    withScope widened (checkJSStatementRaw body)
    restoreAssignmentState preLoopDA
  | .variableDecl (.mk _base declarators kind) =>
    -- Process each declarator (synth init expressions, check against annotation, DA tracking)
    -- Note: declared types and bindings are pre-seeded by checkJSStatements/withScopeAndDeclaredTypes
    for decl in declarators do
      let (.mk _ pat init typeAnn) := decl
      match pat with
      | .identifier id =>
        match typeAnn, init with
        | some annTy, some expr =>
          -- Both annotation and initializer: check init against annotation
          let initTyped ← synthJSExpr expr
          checkAssignable initTyped.type annTy (exprLoc expr) (exprSourceName expr)
          markAssigned id.name
        | _annTy, none =>
          -- No initializer: track for definite assignment if let/const
          match kind with
          | .let_ | .const => requireAssignmentCheck id.name
          | .var => markAssigned id.name
        | none, some expr =>
          -- Initializer only: synth its type
          let _ ← synthJSExpr expr
          markAssigned id.name
      | _ => pure ()
  | .functionDecl _base _id params body _ _ =>
    -- Register function (infer param types as any for JS functions)
    let paramBindings := params.map fun
      | .simple { name, .. } | .withDefault { name, .. } _ | .rest { name, .. } => (name, TSType.any)
      | .pattern _ => ("_", TSType.any)
    -- Save DA state before entering function scope
    let savedDA ← saveAssignmentState
    let savedChecks := (← get).needsAssignmentCheck
    modify fun s => { s with assignedVars := {}, needsAssignmentCheck := {} }
    -- Mark all parameters as assigned
    for (pname, _) in paramBindings do
      markAssigned pname
    let hoisted := collectHoistedVars [.js body]
    let paramNames := paramBindings.map (·.1)
    let hoistedBindings := hoisted.filter (!paramNames.contains ·)
      |>.map fun n => (n, TSType.any)
    withFunctionScope (paramBindings ++ hoistedBindings) none (checkJSStatementRaw body)
    -- Restore outer DA state
    restoreAssignmentState savedDA
    modify fun s => { s with needsAssignmentCheck := savedChecks }
  | .throwStmt _ expr =>
    let _ ← synthJSExpr expr
  | .tryStmt _ block handler finalizer =>
    checkJSStatementRaw block
    match handler with
    | some (.mk _ _ handlerBody _) => checkJSStatementRaw handlerBody
    | none => pure ()
    match finalizer with
    | some fin => checkJSStatementRaw fin
    | none => pure ()
  | .switchStmt _ discriminant cases =>
    let _ ← synthJSExpr discriminant
    let ctx ← read
    let switchKind := Narrowing.analyzeSwitchDiscriminant discriminant
    -- Resolve type aliases in the switch variable's binding so narrowing works on concrete types
    let resolvedBindings ← (match switchKind with
      | .typeofVar varName | .memberAccess varName _ | .directVar varName =>
        match ctx.bindings[varName]? with
        | some ty => do
          let resolved ← resolveTypeGeneric ty
          return ctx.bindings.insert varName resolved
        | none => return ctx.bindings
      | .unknown => return ctx.bindings)
    let mut priorGuards : List Narrowing.Guard := []
    for case_ in cases do
      let (.mk _ test consequent) := case_
      match test with
      | some testExpr =>
        match Narrowing.caseGuard switchKind testExpr with
        | some guard =>
          let narrowed := Narrowing.applyGuard guard resolvedBindings
          withScope (Narrowing.bindingsDiff narrowed ctx.bindings) (checkJSStatements consequent)
          priorGuards := priorGuards ++ [guard]
        | none =>
          checkJSStatements consequent
      | none =>
        -- Default case: apply each prior guard's negation sequentially
        let mut defaultBindings := resolvedBindings
        for guard in priorGuards do
          defaultBindings := Narrowing.applyNegatedGuard guard defaultBindings
        withScope (Narrowing.bindingsDiff defaultBindings ctx.bindings) (checkJSStatements consequent)
  | .forInStmt _ _left right body =>
    let _ ← synthJSExpr right
    let preLoopDA ← saveAssignmentState
    -- Check the body for DA and type errors; no widening since we don't infer iteration type
    checkJSStatementRaw body
    restoreAssignmentState preLoopDA
  | _ => pure ()  -- Graceful degradation for unhandled statements

/-- Process a list of TS statements, threading scope -/
partial def checkStatements (stmts : List TSStatement) : TypeCheckM Unit := do
  match stmts with
  | [] => pure ()
  | stmt :: rest => checkStatement stmt rest

/-- Process a list of JS statements, pre-seeding scope with declared variable names -/
partial def checkJSStatements (stmts : List Statement) : TypeCheckM Unit := do
  -- Pre-seed scope with all variable declarations using annotation types where available
  let extraBindings := stmts.flatMap collectDeclaredBindings
  withScopeAndDeclaredTypes extraBindings (do
    for stmt in stmts do
      checkJSStatementRaw stmt)

end

/-- Type check an entire TS program -/
def checkProgram (prog : TSProgram) : TypeCheckM Unit :=
  checkStatements prog.body

/-- Run the type checker on a TS program, returning diagnostics -/
def typeCheck (prog : TSProgram) (ctx : TypeContext := builtinContext) : Array Diagnostic :=
  runTypeCheckM ctx (checkProgram prog)

-- ─── Throws-annotation inference (TH0060) ─────────────────────────────────

/-- Set of names of every `annotatedFuncDecl` whose `throwsAnn` is
    `.declared _` — i.e., functions that may throw. The type list is
    intentionally not retained here; the type-checker is bool-semantic. -/
private def buildMayThrowEnv (body : List TSStatement) : Std.HashSet String :=
  body.foldl (fun env ts =>
    match ts with
    | .annotatedFuncDecl _ name _ _ _ _ _ _ (.declared _) _ => env.insert name
    | _ => env) {}

mutual

/-- Collect uncaught throw events from a JS statement. An "uncaught throw
    event" is either a direct `throw <expr>` or a call to a `@throws`-
    annotated function, in either case not lexically inside the `try`
    block of an enclosing `try/catch` (try-with-only-finally does not
    consume).

    The walk is exhaustive over `Statement`; every constructor that can
    syntactically contain a throw or a throwing call is handled. Forms
    that introduce a new function scope (`functionDecl`, `classDecl`)
    do NOT recurse — throws inside them belong to the inner function's
    contract, not the enclosing one. -/
private partial def collectUncaughtThrowEvents
    (mayThrow : Std.HashSet String)
    (insideTryCatch : Bool)
    : Statement → List (ThrowSource × Option SourceLocation)
  | .throwStmt base _ =>
      if insideTryCatch then [] else [(.fromThrow, base.loc)]
  | .exprStmt _ expr =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch expr
  | .returnStmt _ (some expr) =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch expr
  | .returnStmt _ none => []
  | .blockStmt _ stmts =>
      stmts.flatMap (collectUncaughtThrowEvents mayThrow insideTryCatch)
  | .ifStmt _ test consequent alternate =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch test
        ++ collectUncaughtThrowEvents mayThrow insideTryCatch consequent
        ++ (match alternate with
            | some alt => collectUncaughtThrowEvents mayThrow insideTryCatch alt
            | none => [])
  | .variableDecl (.mk _ declarators _) =>
      declarators.flatMap fun (.mk _ _ initOpt _) =>
        match initOpt with
        | some expr => collectUncaughtThrowEventsExpr mayThrow insideTryCatch expr
        | none => []
  -- try block: insideTryCatch flips to true ONLY when a catch handler is
  -- present. try-with-only-finally does NOT consume — its block walks with
  -- the outer flag (this is the "tightening" behavior change).
  | .tryStmt _ block handler _finalizer =>
      let blockInsideTry := insideTryCatch || handler.isSome
      let blockEvents := collectUncaughtThrowEvents mayThrow blockInsideTry block
      let handlerEvents := match handler with
        | some (.mk _ _ handlerBody _) =>
            collectUncaughtThrowEvents mayThrow insideTryCatch handlerBody
        | none => []
      blockEvents ++ handlerEvents
  | .switchStmt _ discriminant cases =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch discriminant
        ++ cases.flatMap fun (.mk _ testOpt body) =>
            (match testOpt with
              | some t => collectUncaughtThrowEventsExpr mayThrow insideTryCatch t
              | none => [])
            ++ body.flatMap (collectUncaughtThrowEvents mayThrow insideTryCatch)
  | .labeledStmt _ _ inner =>
      collectUncaughtThrowEvents mayThrow insideTryCatch inner
  | .withStmt _ obj body =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch obj
        ++ collectUncaughtThrowEvents mayThrow insideTryCatch body
  | .whileStmt _ test body =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch test
        ++ collectUncaughtThrowEvents mayThrow insideTryCatch body
  | .doWhileStmt _ body test =>
      collectUncaughtThrowEvents mayThrow insideTryCatch body
        ++ collectUncaughtThrowEventsExpr mayThrow insideTryCatch test
  | .forStmt _ init test update body =>
      let initEvents := match init with
        | some (.inl e) => collectUncaughtThrowEventsExpr mayThrow insideTryCatch e
        | some (.inr (.mk _ decls _)) =>
            decls.flatMap fun (.mk _ _ initOpt _) =>
              match initOpt with
              | some e => collectUncaughtThrowEventsExpr mayThrow insideTryCatch e
              | none => []
        | none => []
      let testEvents := match test with
        | some t => collectUncaughtThrowEventsExpr mayThrow insideTryCatch t
        | none => []
      let updateEvents := match update with
        | some u => collectUncaughtThrowEventsExpr mayThrow insideTryCatch u
        | none => []
      initEvents ++ testEvents ++ updateEvents
        ++ collectUncaughtThrowEvents mayThrow insideTryCatch body
  | .forInStmt _ _ right body =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch right
        ++ collectUncaughtThrowEvents mayThrow insideTryCatch body
  | .forOfStmt _ _ right body _ =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch right
        ++ collectUncaughtThrowEvents mayThrow insideTryCatch body
  -- Statements with no body or no events.
  | .emptyStmt _ | .breakStmt _ _ | .continueStmt _ _ | .debuggerStmt _ => []
  -- Inner function/class declarations introduce a new scope; throws inside
  -- them belong to that inner contract, not this enclosing function.
  | .functionDecl .. | .classDecl .. => []

private partial def collectUncaughtThrowEventsExpr
    (mayThrow : Std.HashSet String)
    (insideTryCatch : Bool)
    : Expression → List (ThrowSource × Option SourceLocation)
  | .callExpr base (.identifier _ calleeName) args _ =>
      let here : List (ThrowSource × Option SourceLocation) :=
        if !insideTryCatch && mayThrow.contains calleeName then
          [(.fromCall calleeName, base.loc)]
        else []
      let argEvents := args.flatMap (collectUncaughtThrowEventsExpr mayThrow insideTryCatch)
      here ++ argEvents
  | .callExpr _ callee args _ =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch callee
        ++ args.flatMap (collectUncaughtThrowEventsExpr mayThrow insideTryCatch)
  | .newExpr _ callee args =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch callee
        ++ args.flatMap (collectUncaughtThrowEventsExpr mayThrow insideTryCatch)
  | .binaryExpr _ _ l r =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch l
        ++ collectUncaughtThrowEventsExpr mayThrow insideTryCatch r
  | .logicalExpr _ _ l r =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch l
        ++ collectUncaughtThrowEventsExpr mayThrow insideTryCatch r
  | .assignmentExpr _ _ l r =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch l
        ++ collectUncaughtThrowEventsExpr mayThrow insideTryCatch r
  | .conditionalExpr _ test cons alt =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch test
        ++ collectUncaughtThrowEventsExpr mayThrow insideTryCatch cons
        ++ collectUncaughtThrowEventsExpr mayThrow insideTryCatch alt
  | .memberExpr _ obj prop _ _ =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch obj
        ++ collectUncaughtThrowEventsExpr mayThrow insideTryCatch prop
  | .unaryExpr _ _ _ arg | .updateExpr _ _ arg _ | .spreadElement _ arg
  | .chainExpr _ arg | .awaitExpr _ arg =>
      collectUncaughtThrowEventsExpr mayThrow insideTryCatch arg
  | .yieldExpr _ argOpt _ =>
      match argOpt with
      | some arg => collectUncaughtThrowEventsExpr mayThrow insideTryCatch arg
      | none => []
  | .arrayExpr _ elements =>
      elements.flatMap fun
        | some e => collectUncaughtThrowEventsExpr mayThrow insideTryCatch e
        | none => []
  | .sequenceExpr _ exprs =>
      exprs.flatMap (collectUncaughtThrowEventsExpr mayThrow insideTryCatch)
  | .templateLiteral _ _ exprs =>
      exprs.flatMap (collectUncaughtThrowEventsExpr mayThrow insideTryCatch)
  | _ => []

end

/-- For every `annotatedFuncDecl` whose `throwsAnn = .absent` and which is
    not `@total`, emit TH0060 at the location of each uncaught throw event.
    `@total` functions are excluded here because TH0067 (`totalHasUncaughtThrow`)
    is the more specific diagnostic for that case. -/
def throwsAnnotationCheck (prog : TSProgram) : Array Diagnostic :=
  let mayThrow := buildMayThrowEnv prog.body
  prog.body.foldl (fun acc ts =>
    match ts with
    | .annotatedFuncDecl _ _ _ _ _ body _ _ .absent false =>
        let events := collectUncaughtThrowEvents mayThrow false body
        events.foldl (fun acc2 (src, loc) =>
          acc2.push { kind := .thales (.unannotatedThrow src), location := loc }) acc
    | _ => acc) #[]

/-- Reject `@throws` with no type list (v1 requirement; future work covers
    body-inference). Emits TH0065 at the function's declaration location. -/
def throwsTypeListCheck (prog : TSProgram) : Array Diagnostic :=
  prog.body.foldl (fun acc ts =>
    match ts with
    | .annotatedFuncDecl base _ _ _ _ _ _ _ (.declared []) _ =>
        acc.push { kind := .thales .throwsRequiresTypeList, location := base.loc }
    | _ => acc) #[]

/-- Enforce that `@total` functions have no observable failure modes.

    Two diagnostics:
    * **TH0066** — `@total` and `@throws` are both declared on the same
      function. The annotations contradict each other; emitted at the
      function's declaration location.
    * **TH0067** — the function is `@total` (without `@throws`) but its
      body contains an uncaught throw event. Emitted at each event's
      location. A throw inside a `try` whose `catch` itself contains a
      throw still surfaces, because `collectUncaughtThrowEvents` walks
      the catch handler with the outer `insideTryCatch` flag. -/
def totalAnnotationCheck (prog : TSProgram) : Array Diagnostic :=
  let mayThrow := buildMayThrowEnv prog.body
  prog.body.foldl (fun acc ts =>
    match ts with
    | .annotatedFuncDecl base _ _ _ _ _ _ _ (.declared _) true =>
        acc.push { kind := .thales .totalConflictsWithThrows, location := base.loc }
    | .annotatedFuncDecl _ _ _ _ _ body _ _ .absent true =>
        let events := collectUncaughtThrowEvents mayThrow false body
        events.foldl (fun acc2 (src, loc) =>
          acc2.push { kind := .thales (.totalHasUncaughtThrow src), location := loc }) acc
    | _ => acc) #[]

end Thales.TypeCheck
