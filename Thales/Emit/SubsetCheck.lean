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
  /-- Inside a `@total` function body. while/do-while (and while-desugared
      `for`) lower to a partial-backed combinator the termination verifier
      cannot see through, so they draw TH0068 here instead of being
      admitted. -/
  inTotalFn : Bool := false
  /-- Type alias environment threaded from the enclosing `annotatedFuncDecl`
      context; used to resolve array types for for-of admission. -/
  aliasEnv : Std.HashMap String TSType := {}
  /-- Binding environment for the enclosing function's typed parameters;
      used to check that for-of RHS resolves to an array type. -/
  bindingEnv : Std.HashMap String TSType := {}
  /-- Annotation-derived types of identifiers in scope (module-level consts,
      typed parameters, body-local typed declarators), used solely to resolve
      an array-method receiver's element type for TH0085. Kept separate from
      `bindingEnv` on purpose: `bindingEnv` feeds the intentionally
      conservative (params-only) loop-admission check, which must not widen. -/
  recvEnv : Std.HashMap String TSType := {}

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

/-- True iff the enclosing context can admit an emittable loop shape (#25):
    inside a declared function whose body is do-mode lowerable, outside
    `@throws`/try zones. The per-loop syntactic shape check is separate
    (`LoopShape.classifyLoop`). -/
private def loopContextAdmitted (ctx : MutCtx) : Bool :=
  match ctx.info with
  | none => false
  | some info => info.doModeLowerable && !ctx.noMutZone && ctx.allowEligible

/-- Shared gate for the while-family loop arms (`while`, `do`/`while`,
    desugared `for`): an admitted loop inside `@total` draws TH0068 — its
    lowering is partial-backed, so the lake-side termination verification
    would pass vacuously — otherwise the operand checks run. An unadmitted
    loop is exactly one TH0010, no operand recursion. -/
private def checkAdmittedLoop (ctx : MutCtx) (loc : Option SourceLocation)
    (admitted : Bool) (operands : Unit → Array Diagnostic)
    : Array Diagnostic :=
  if admitted then
    if ctx.inTotalFn then #[mkThalesDiag .totalHasUnverifiableLoop loc]
    else operands ()
  else
    #[mkThalesDiag .loopNotSupported loc]

/-- Resolve a TSType through type alias references.
    Follows at most one level of .ref to avoid infinite loops in v1. -/
private def resolveType (aliasEnv : Std.HashMap String TSType) : TSType → TSType
  | .ref name _ =>
    match aliasEnv.get? name with
    | some resolved => resolved
    | none => .ref name []
  | .paren inner => resolveType aliasEnv inner
  | other => other

/-- The identifier's declared type resolves to an array in the enclosing
    function's parameter environment. Conservative (params-only):
    body-declared arrays do not resolve — widening them is a future task.
    Non-array iterables/bounds (string, Map, generator, …) must stay
    rejected: their Lean lowerings diverge semantically (e.g. `Char` vs
    1-char string, codepoint vs UTF-16 length). -/
private def identIsArray (ctx : MutCtx) (name : String) : Bool :=
  match ctx.bindingEnv.get? name with
  | some ty =>
      match resolveType ctx.aliasEnv ty with
      | .array _ => true
      | _ => false
  | none => false

/-- Record a statement's body-local typed declarators into `recvEnv` so a
    later array-method call on them can resolve the element type (TH0085).
    Only explicit annotations are tracked; resolving inferred/initializer-shape
    types is the emitter's job and is tracked separately. -/
private def recordRecvDecls (ctx : MutCtx) (s : Statement) : MutCtx :=
  match s with
  | .variableDecl (VariableDeclaration.mk _ decls _) =>
      decls.foldl (fun ctx decl =>
        match decl with
        | VariableDeclarator.mk _ (.identifier idn) _ (some ty) =>
            { ctx with recvEnv := ctx.recvEnv.insert idn.name ty }
        | _ => ctx) ctx
  | _ => ctx

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
            || info.nullTested.contains name
            || !info.doModeLowerable then
      -- Still-rejected forms: `let` without initializer, variables whose
      -- narrowing the emitter relies on (refinement-tested or
      -- null/undefined-tested — mutating through the match arm's pattern
      -- rebinding is #36), and functions whose body contains a shape
      -- do-mode can't lower — an unlowerable switch, a `try`/`catch`
      -- (#41), or a narrowing-dependent read the emitter cannot rebind.
      -- `doModeLowerable` is the same predicate `emitFuncDecl` gates on;
      -- the two must never disagree.
      #[mkThalesDiag (.cannotReassignVariable name) loc]
    else if ctx.allowEligible && emittable then
      -- Eligible mutation (`=`, arithmetic `OP=`, `++`/`--`) in a declared
      -- function body: in subset, lowered to `Id.run do` by the emitter.
      #[]
    else
      #[mkThalesDiag (.cannotReassignVariable name) loc]

/-- Member names that collide with the members Lean auto-generates for a
    `structure` (rejected on v1 class fields and methods). -/
private def leanReservedMemberNames : List String :=
  ["mk", "rec", "recOn", "casesOn", "brecOn", "below", "ibelow",
   "noConfusion", "noConfusionType"]

/-- The plain-identifier name of a class member key, if any. -/
private def classKeyName? : Expression → Option String
  | .identifier _ n => some n
  | _ => none

/-- A non-computed member-property reference found in an expression/statement
    tree. `isDirectCallee` is true only when the member expression is the
    callee of a call (`recv.m(...)`), the one position where a v1 class
    method may be referenced; `thisBase` marks `this.<prop>` references.
    Drives TH0101 (forward references), TH0102 (method used as a value), and
    the ctor read-before-assign scan. -/
private structure MemberPropRef where
  prop : String
  loc : Option SourceLocation
  isDirectCallee : Bool
  thisBase : Bool

mutual

private partial def memberPropRefsExpr (inCallee : Bool) :
    Expression → List MemberPropRef
  | .memberExpr mb obj prop computed _ =>
      let own := match prop with
        | .identifier _ p =>
          if computed then []
          else [{ prop := p, loc := mb.loc, isDirectCallee := inCallee,
                  thisBase := match obj with | .thisExpr _ => true | _ => false }]
        | _ => []
      own ++ memberPropRefsExpr false obj
        ++ (if computed then memberPropRefsExpr false prop else [])
  | .callExpr _ callee args _ =>
      memberPropRefsExpr true callee ++ args.flatMap (memberPropRefsExpr false)
  | .newExpr _ callee args =>
      memberPropRefsExpr false callee ++ args.flatMap (memberPropRefsExpr false)
  | .identifier _ _ | .literal _ _ _ | .thisExpr _ | .super_ _
  | .metaProperty _ _ _ | .patternExpr _ _ => []
  | .arrayExpr _ els => els.flatMap fun
      | some e => memberPropRefsExpr false e
      | none => []
  | .objectExpr _ props => props.flatMap fun
      | .regular _ k v _ computed _ =>
          (if computed then memberPropRefsExpr false k else []) ++ memberPropRefsExpr false v
      | .spread _ a => memberPropRefsExpr false a
  | .functionExpr _ _ _ body _ _ => memberPropRefsStmt body
  | .arrowFunctionExpr _ _ body _ _ _ =>
      match body with
      | .inl e => memberPropRefsExpr false e
      | .inr s => memberPropRefsStmt s
  | .unaryExpr _ _ _ a | .updateExpr _ _ a _ | .spreadElement _ a
  | .awaitExpr _ a | .chainExpr _ a | .privateMemberExpr _ a _ => memberPropRefsExpr false a
  | .binaryExpr _ _ l r | .assignmentExpr _ _ l r | .logicalExpr _ _ l r =>
      memberPropRefsExpr false l ++ memberPropRefsExpr false r
  | .conditionalExpr _ t c a =>
      memberPropRefsExpr false t ++ memberPropRefsExpr false c ++ memberPropRefsExpr false a
  | .sequenceExpr _ es => es.flatMap (memberPropRefsExpr false)
  | .templateLiteral _ _ es => es.flatMap (memberPropRefsExpr false)
  | .taggedTemplate _ t q => memberPropRefsExpr false t ++ memberPropRefsExpr false q
  | .classExpr _ _ _ body .. => body.flatMap memberPropRefsElement
  | .yieldExpr _ a _ => match a with
      | some e => memberPropRefsExpr false e
      | none => []

private partial def memberPropRefsElement :
    ClassElement → List MemberPropRef
  | .method (.mk _ _ value ..) => memberPropRefsExpr false value
  | .field (.mk _ _ value ..) => match value with
      | some e => memberPropRefsExpr false e
      | none => []
  | .staticBlock _ body => body.flatMap memberPropRefsStmt

private partial def memberPropRefsStmt :
    Statement → List MemberPropRef
  | .exprStmt _ e | .throwStmt _ e => memberPropRefsExpr false e
  | .blockStmt _ b => b.flatMap memberPropRefsStmt
  | .ifStmt _ t c a =>
      memberPropRefsExpr false t ++ memberPropRefsStmt c
        ++ (match a with | some s => memberPropRefsStmt s | none => [])
  | .returnStmt _ a => match a with
      | some e => memberPropRefsExpr false e
      | none => []
  | .variableDecl (.mk _ decls _) =>
      decls.flatMap fun (.mk _ _ init _) => match init with
        | some e => memberPropRefsExpr false e
        | none => []
  | .whileStmt _ t b => memberPropRefsExpr false t ++ memberPropRefsStmt b
  | .doWhileStmt _ b t => memberPropRefsStmt b ++ memberPropRefsExpr false t
  | .forStmt _ init t u b =>
      (match init with
       | some (.inl e) => memberPropRefsExpr false e
       | some (.inr (.mk _ decls _)) =>
           decls.flatMap fun (.mk _ _ i _) => match i with
             | some e => memberPropRefsExpr false e
             | none => []
       | none => [])
      ++ (match t with | some e => memberPropRefsExpr false e | none => [])
      ++ (match u with | some e => memberPropRefsExpr false e | none => [])
      ++ memberPropRefsStmt b
  | .forInStmt _ left r b | .forOfStmt _ left r b _ =>
      (match left with | .inl e => memberPropRefsExpr false e | .inr _ => [])
        ++ memberPropRefsExpr false r ++ memberPropRefsStmt b
  | .switchStmt _ d cases =>
      memberPropRefsExpr false d ++ cases.flatMap (fun (.mk _ t ss) =>
        (match t with | some e => memberPropRefsExpr false e | none => [])
          ++ ss.flatMap memberPropRefsStmt)
  | .tryStmt _ b h f =>
      memberPropRefsStmt b
        ++ (match h with | some (.mk _ _ hb _) => memberPropRefsStmt hb | none => [])
        ++ (match f with | some s => memberPropRefsStmt s | none => [])
  | .labeledStmt _ _ b | .withStmt _ _ b => memberPropRefsStmt b
  | .functionDecl _ _ _ body _ _ => memberPropRefsStmt body
  | .classDecl _ _ _ body .. => body.flatMap memberPropRefsElement
  | _ => []

end

/-- First `this.<p>` read in an expression whose `p` is not in `assigned` —
    the read-before-assign scan for v1 constructor bodies. Nested functions/
    arrows are scanned too (their `this` is the same instance for arrows, and
    a conservative reject is safe either way). -/
private def findUnassignedThisRead (e : Expression) (assigned : List String) : Option String :=
  (memberPropRefsExpr false e).findSome? fun r =>
    if r.thisBase && !assigned.contains r.prop then some r.prop else none

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
        -- TH0085: join/indexOf/includes lower only when the emitter can
        -- statically resolve the receiver to `number[]`/`string[]`. Reject the
        -- two receiver shapes that would otherwise emit uncompilable Lean:
        --   (a) a non-identifier receiver (call result, member chain, …);
        --   (b) an identifier whose declared element type is an array of some
        --       other type (`boolean[]`, `number[][]`, an object array, …).
        -- Receivers SubsetCheck cannot resolve here (string methods, arrays
        -- whose type is only inferred from an initializer) are left to the
        -- existing path and tracked under separate issues.
        else if propName == "join" || propName == "indexOf" || propName == "includes"
            || propName == "lastIndexOf" || propName == "some" || propName == "every"
            || propName == "findIndex" then
          match obj with
          | .identifier _ recv =>
              match (ctx.recvEnv.get? recv).map (resolveType ctx.aliasEnv) with
              | some (.array .number) => checkExpr ctx callee
              | some (.array .string) => checkExpr ctx callee
              | some (.array _) =>
                  #[mkThalesDiag (.arrayMethodReceiverNotLowerable propName) loc]
                    ++ checkExpr ctx obj
              | _ => checkExpr ctx callee
          | _ =>
              #[mkThalesDiag (.arrayMethodReceiverNotLowerable propName) loc]
                ++ checkExpr ctx obj
        else
          checkExpr ctx callee
      | _ => checkExpr ctx callee
    calleeDiags ++ (arguments.foldl (fun acc arg => acc ++ checkExpr ctx arg) #[])
  | .unaryExpr base op _ argument =>
    let opDiag : Array Diagnostic :=
      match op with
      | .typeof => #[mkThalesDiag (.unsupportedUnaryOperator "typeof") base.loc]
      | .void   => #[mkThalesDiag (.unsupportedUnaryOperator "void") base.loc]
      | .delete => #[mkThalesDiag (.unsupportedUnaryOperator "delete") base.loc]
      | _       => #[]
    opDiag ++ checkExpr ctx argument
  | .binaryExpr b _ left right =>
    -- TH0084: a definedness test on a body-local whose type the emitter
    -- cannot record (not a param, not in `typedDecls`) can be neither
    -- folded nor narrowed, so reject rather than emit uncompilable Lean.
    -- Params and top-level bindings are recordable, so they never reach here.
    let th84 : Array Diagnostic :=
      match ctx.info with
      | some info =>
        match EscapeAnalysis.definednessTestSubject? expr with
        | some subj =>
          let isBodyLocal := info.initializedLets.contains subj
            || info.uninitializedLets.contains subj || info.consts.contains subj
          let isRecordable := info.params.contains subj || info.typedDecls.contains subj
          if isBodyLocal && !isRecordable then
            #[mkThalesDiag .definednessTestUnrecordedBinding b.loc]
          else #[]
        | none => #[]
      | none => #[]
    -- TH0086: a definedness test whose subject is a non-identifier expression
    -- (call, member access, computed index) cannot be narrowed by the emitter,
    -- which would emit a literal `undefined`/`.none`. Independent of TH0084,
    -- which only fires on identifier subjects.
    let th86 : Array Diagnostic :=
      if EscapeAnalysis.definednessTestHasNonIdentifierSubject expr then
        #[mkThalesDiag .definednessTestNonIdentifierSubject b.loc]
      else #[]
    th84 ++ th86 ++ checkExpr ctx left ++ checkExpr ctx right
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
  | .classExpr b _ superClass .. =>
    let baseDiag := #[mkThalesDiag (.classNotSupported "class expressions") b.loc]
    match superClass with
    | some _ => baseDiag ++ #[mkThalesDiag .inheritanceNotSupported b.loc]
    | none => baseDiag
  -- Leaf nodes with no sub-expressions
  | .identifier _ _ => #[]
  | .literal base (.regex _ _) _ => #[mkThalesDiag .regexLiteral base.loc]
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
    -- Thread `recvEnv` so a body-local typed array declarator is visible to a
    -- later array-method call on it (TH0085); declarations stay scoped to the
    -- block because the accumulator resets per `checkStmt` recursion.
    (body.foldl (fun (st : Array Diagnostic × MutCtx) s =>
      (st.1 ++ checkStmt st.2 s, recordRecvDecls st.2 s)) (#[], ctx)).1
  | .ifStmt _ test consequent alternate =>
    checkExpr ctx test
      ++ checkStmt ctx consequent
      ++ (match alternate with | some s => checkStmt ctx s | none => #[])
  -- TH0010: loop statements. A loop is admitted (no TH0010, recurse into
  -- the body) iff `loopContextAdmitted` holds AND `classifyLoop` admits its
  -- shape AND its array operand (for-of RHS / length bound) passes
  -- `identIsArray`; otherwise exactly one TH0010 and no body recursion.
  -- doModeLowerable keeps the phases agreeing: a function holding both an
  -- admitted-shape loop and an unlowerable one (labeled break/continue,
  -- do-while with loop-level `continue`) rejects BOTH loops.
  --
  -- while has no per-loop shape conditions beyond what EscapeAnalysis
  -- already folded into `doModeLowerable` (labels poison it there).
  | .whileStmt b test body =>
    checkAdmittedLoop ctx b.loc (loopContextAdmitted ctx) fun _ =>
      checkExpr ctx test ++ checkStmt ctx body
  -- A do-while loop-level `continue` is rejected here, not only via
  -- EscapeAnalysis poisoning: TS `continue` jumps to the test, but the
  -- `repeat … until` lowering re-enters the body without checking it.
  | .doWhileStmt b body test =>
    checkAdmittedLoop ctx b.loc
      (loopContextAdmitted ctx && !LoopShape.hasOwnUnlabeledContinue body)
      fun _ => checkStmt ctx body ++ checkExpr ctx test
  | .forInStmt b _ _ _ =>
    #[mkThalesDiag .loopNotSupported b.loc]
  | s@(.forStmt b _ _ _ body) =>
    let canonicalAdmitted :=
      match LoopShape.classifyLoop s with
      | .canonicalFor _ (.inl _) _ => true
      | .canonicalFor _ (.inr arrName) _ => identIsArray ctx arrName
      | _ => false
    if loopContextAdmitted ctx && canonicalAdmitted then
      -- Only the body: classifyLoop already constrained init/test/update to
      -- bare shapes, and routing `i++` through checkExpr would draw
      -- .assignmentInExpressionPosition.
      checkStmt ctx body
    else
      match LoopShape.desugarGeneralFor s with
      | some desugared =>
        if loopContextAdmitted ctx then
          -- Check the statements the emitter will actually lower: init and
          -- update land in STATEMENT position (so `i -= 2` routes through
          -- the statement-position mutation rules, not
          -- .assignmentInExpressionPosition) and the while arm supplies
          -- the `@total` gate (TH0068).
          desugared.foldl (fun acc d => acc ++ checkStmt ctx d) #[]
        else
          #[mkThalesDiag .loopNotSupported b.loc]
      | none =>
        #[mkThalesDiag .loopNotSupported b.loc]
  | s@(.forOfStmt b _ right body _) =>
    let rhsIsArray : Bool :=
      match right with
      | .arrayExpr _ _ => true
      | .identifier _ n => identIsArray ctx n
      | _ => false
    let admitted :=
      rhsIsArray
        && loopContextAdmitted ctx
        && (match LoopShape.classifyLoop s with
            | .forOf _ _ _ _ => true
            | _ => false)
    if admitted then
      -- The loop binder is part of the admitted shape; check only the RHS
      -- expression and the body.
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
  -- Class declarations: per-member v1 validation (TH0030 narrows to
  -- unsupported class forms; members draw TH0094-TH0102)
  | .classDecl b _ superClass body isAbstract hasTypeParams hasImplements =>
    checkClassDecl ctx b superClass body isAbstract hasTypeParams hasImplements

/-- Validate a class declaration against the v1 supported shape (#106):
    readonly annotated fields, an assign-each-field-once constructor, public
    non-static instance methods with return annotations. Class-level form
    violations (abstract/generic/implements/extends) short-circuit member
    validation. General subset checks recurse into ctor and method bodies. -/
partial def checkClassDecl (ctx : MutCtx) (b : NodeBase) (superClass : Option Expression)
    (body : List ClassElement) (isAbstract hasTypeParams hasImplements : Bool)
    : Array Diagnostic := Id.run do
  -- Class-level form: wrong form makes member-level precision meaningless
  let classLevel : Array Diagnostic :=
    (if isAbstract then #[mkThalesDiag (.classNotSupported "abstract classes") b.loc] else #[])
    ++ (if hasTypeParams then #[mkThalesDiag (.classNotSupported "generic classes") b.loc] else #[])
    ++ (if hasImplements then #[mkThalesDiag (.classNotSupported "'implements' clauses") b.loc] else #[])
    ++ (match superClass with
        | some _ => #[mkThalesDiag .inheritanceNotSupported b.loc]
        | none => #[])
  if !classLevel.isEmpty then
    return classLevel
  -- Declared instance fields/methods reachable via `this.<name>` (identifier
  -- keys, non-static, not `#`-private — the latter draw TH0096 on their own)
  let fieldNames : List String := body.filterMap fun
    | .field (.mk _ key _ false false none ..) => classKeyName? key
    | _ => none
  let methodNames : List String := body.filterMap fun
    | .method (.mk _ key _ .method false false none ..) => classKeyName? key
    | _ => none
  let isPrivate (accessibility : Option Accessibility) : Bool :=
    accessibility == some .private_ || accessibility == some .protected_
  let mut diags : Array Diagnostic := #[]
  let mut ctorCount : Nat := 0
  for el in body do
    match el with
    | .staticBlock sb _ =>
      diags := diags.push (mkThalesDiag .classStaticNotSupported sb.loc)
    | .field (.mk fb key value computed static_ privateName readonly optional typeAnnotation accessibility) =>
      let loc := fb.loc
      if static_ then
        diags := diags.push (mkThalesDiag .classStaticNotSupported loc)
      else if privateName.isSome || isPrivate accessibility then
        diags := diags.push (mkThalesDiag .classPrivateMemberNotSupported loc)
      else if value.isSome then
        diags := diags.push (mkThalesDiag .classFieldInitializerNotSupported loc)
      else if computed || (classKeyName? key).isNone then
        diags := diags.push (mkThalesDiag (.classFieldFormNotSupported "computed names are not supported") loc)
      else if !readonly then
        diags := diags.push (mkThalesDiag (.classFieldFormNotSupported "must be declared readonly") loc)
      else if optional then
        diags := diags.push (mkThalesDiag (.classFieldFormNotSupported "optional fields are not supported") loc)
      else if typeAnnotation.isNone then
        diags := diags.push (mkThalesDiag (.classFieldFormNotSupported "missing type annotation") loc)
      else if let some n := classKeyName? key then
        if leanReservedMemberNames.contains n then
          diags := diags.push (mkThalesDiag (.classFieldFormNotSupported s!"'{n}' is a reserved name") loc)
    | .method (.mk mb key value kind computed static_ privateName accessibility override_ optional hasTPs sigParams returnType) =>
      let loc := mb.loc
      let bodyCtx (params : List FunctionParam) (mbody : Statement) : MutCtx :=
        { ctx with info := some (nestedInfo params mbody), allowEligible := false }
      match kind with
      | .getter | .setter =>
        diags := diags.push (mkThalesDiag .classAccessorNotSupported loc)
      | .constructor =>
        ctorCount := ctorCount + 1
        if isPrivate accessibility then
          diags := diags.push (mkThalesDiag .classPrivateMemberNotSupported loc)
        else if ctorCount > 1 then
          diags := diags.push (mkThalesDiag (.classCtorFormNotSupported "a class must declare exactly one constructor") loc)
        else if sigParams.any (fun (pname, ann, opt, rest_) =>
            pname == "_destructured" || opt || rest_ || ann.isNone) then
          diags := diags.push (mkThalesDiag (.classCtorFormNotSupported "parameters must be plain annotated identifiers") loc)
        else if let .functionExpr _ _ params cbody _ _ := value then
          -- Straight-line body: each statement must be `this.<field> = <expr>;`,
          -- each declared field assigned exactly once, `this.<x>` reads in an
          -- RHS only after `x` was assigned. General checks recurse into RHSs
          -- (and, for non-conforming statements, the whole statement).
          let ctx' := bodyCtx params cbody
          let stmts := match cbody with
            | .blockStmt _ ss => ss
            | s => [s]
          let mut assigned : List String := []
          let mut ctorDiag : Option ThalesKind := none
          for s in stmts do
            match s with
            | .exprStmt _ (.assignmentExpr _ .assign (.memberExpr _ (.thisExpr _) (.identifier _ f) false _) rhs) =>
              if !fieldNames.contains f || assigned.contains f then
                if ctorDiag.isNone then
                  ctorDiag := some (.classCtorFormNotSupported s!"field '{f}' must be assigned exactly once")
              else
                -- `this.<x>` reads in the RHS must target already-assigned fields
                match findUnassignedThisRead rhs assigned with
                | some p =>
                  if ctorDiag.isNone then
                    ctorDiag := some (.classCtorFormNotSupported s!"field '{p}' is read before it is assigned")
                | none => pure ()
                assigned := assigned ++ [f]
              diags := diags ++ checkExpr ctx' rhs
            | _ =>
              if ctorDiag.isNone then
                ctorDiag := some (.classCtorFormNotSupported "body must be a sequence of this.<field> = <expr> assignments")
              diags := diags ++ checkStmt ctx' s
          if ctorDiag.isNone then
            if let some missing := fieldNames.find? (fun f => !assigned.contains f) then
              ctorDiag := some (.classCtorFormNotSupported s!"field '{missing}' must be assigned exactly once")
          if let some k := ctorDiag then
            diags := diags.push (mkThalesDiag k loc)
      | .method =>
        let isGenAsync := match value with
          | .functionExpr _ _ _ _ gen async => gen || async
          | _ => false
        if static_ then
          diags := diags.push (mkThalesDiag .classStaticNotSupported loc)
        else if privateName.isSome || isPrivate accessibility then
          diags := diags.push (mkThalesDiag .classPrivateMemberNotSupported loc)
        else if isGenAsync then
          diags := diags.push (mkThalesDiag (.classMethodFormNotSupported "generator and async methods are not supported") loc)
        else if computed || (classKeyName? key).isNone then
          diags := diags.push (mkThalesDiag (.classMethodFormNotSupported "computed names are not supported") loc)
        else if optional then
          diags := diags.push (mkThalesDiag (.classMethodFormNotSupported "optional methods are not supported") loc)
        else if hasTPs then
          diags := diags.push (mkThalesDiag (.classMethodFormNotSupported "generic methods are not supported") loc)
        else if override_ then
          diags := diags.push (mkThalesDiag (.classMethodFormNotSupported "'override' is not supported") loc)
        else if returnType.isNone then
          diags := diags.push (mkThalesDiag (.classMethodFormNotSupported "missing return type annotation") loc)
        else if let some n := classKeyName? key then
          if leanReservedMemberNames.contains n then
            diags := diags.push (mkThalesDiag (.classMethodFormNotSupported s!"'{n}' is a reserved name") loc)
        -- General subset checks recurse into the method body regardless of
        -- the signature verdict; forward references draw TH0101.
        if let .functionExpr _ _ params mbody _ _ := value then
          let mIdx := (classKeyName? key).bind (fun n => methodNames.idxOf? n)
          let laterMethods := match mIdx with
            | some i => methodNames.drop (i + 1)
            | none => []
          for r in memberPropRefsStmt mbody do
            if laterMethods.contains r.prop then
              diags := diags.push (mkThalesDiag (.classMethodForwardReference r.prop) r.loc)
          diags := diags ++ checkStmt (bodyCtx params mbody) mbody
  -- A class with fields must declare a constructor
  if ctorCount == 0 && !fieldNames.isEmpty then
    diags := diags.push (mkThalesDiag (.classCtorFormNotSupported "a class with fields must declare a constructor") b.loc)
  return diags

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

/-- Module-level annotation-derived bindings (top-level typed `const`/`let`),
    seeded into `recvEnv` for the array-method receiver check (TH0085). -/
private def buildTopRecvEnv (body : List TSStatement) : Std.HashMap String TSType :=
  body.foldl (fun env ts =>
    match ts with
    | .annotatedVarDecl _ _ name (some ann) _ => env.insert name ann.type
    | .declareStmt _ (.annotatedVarDecl _ _ name (some ann) _) => env.insert name ann.type
    | _ => env) {}

/-- Build a binding environment from annotated function parameters. -/
private def buildParamEnv
    (params : List (String × Option TypeAnnotation × Bool × Bool))
    : Std.HashMap String TSType :=
  params.foldl (fun env (name, annOpt, _, _) =>
    match annOpt with
    | some ann => env.insert name ann.type
    | none => env) {}

/-- Check a TS-level statement for mutation violations.
    `aliasEnv` is threaded in for for-of array-type resolution; `topRecvEnv`
    carries module-level annotation types for the TH0085 receiver check. -/
def checkTSStmt (aliasEnv : Std.HashMap String TSType)
    (topRecvEnv : Std.HashMap String TSType)
    (moduleInfo : EscapeAnalysis.MutationInfo) (ts : TSStatement) : Array Diagnostic :=
  match ts with
  | .js s =>
    -- Module-level executable statement: admit the same mutation (#24) and
    -- loop (#25) subset as a function body, using the whole-module mutation
    -- info. `bindingEnv` is empty (no params at module level), so for-of over
    -- a named array stays out of v1 — array literals still lower (#49).
    let ctx : MutCtx :=
      { aliasEnv := aliasEnv, recvEnv := topRecvEnv,
        info := some moduleInfo, allowEligible := true,
        noMutZone := false, inTotalFn := false, bindingEnv := {} }
    checkStmt ctx s ++ shadowStmts {} [s]
  | .annotatedVarDecl b _ _ typeAnn initOpt =>
    checkAnn b.loc typeAnn
      ++ (match initOpt with
          | some e => checkExpr {} e ++ shadowExpr e
          | none => #[])
  -- TH0012: async annotated function declarations — emit diagnostic, still recurse body.
  -- TH0060 is no longer SubsetCheck's responsibility, so no suppression filter is needed.
  | .annotatedFuncDecl b _ _ params returnType body _ async throwsAnn isTotal =>
    let paramEnv := buildParamEnv params
    let ctx : MutCtx :=
      { info := some (EscapeAnalysis.analyze (params.map (·.1)) body),
        noMutZone := throwsAnn != .absent,
        allowEligible := true,
        inTotalFn := isTotal,
        aliasEnv := aliasEnv,
        bindingEnv := paramEnv,
        -- Typed params override module-level bindings of the same name.
        recvEnv := paramEnv.fold (fun m k v => m.insert k v) topRecvEnv }
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
  | .declareStmt _ inner => checkTSStmt aliasEnv topRecvEnv moduleInfo inner
  | .importDecl b _ _ form _ =>
    match form with
    | .named => #[]
    | .defaultImport => #[mkThalesDiag (.unsupportedImportForm "default import") b.loc]
    | .namespaceImport => #[mkThalesDiag (.unsupportedImportForm "import * as ns") b.loc]
    | .sideEffect => #[mkThalesDiag (.unsupportedImportForm "side-effect import") b.loc]
  | .exportDecl _ inner => checkTSStmt aliasEnv topRecvEnv moduleInfo inner
  | .exportNamedDecl _ _ => #[]
  | .exportUnsupported b form =>
    match form with
    | .defaultExport => #[mkThalesDiag (.unsupportedExportForm "export default") b.loc]
    | .reexport => #[mkThalesDiag (.unsupportedExportForm "re-export") b.loc]

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

private def fvInsert (s : Std.HashSet String) (xs : List String) : Std.HashSet String :=
  xs.foldl (·.insert ·) s

/-- Identifiers a `Pattern` binds — descending through object/array
    destructuring, defaults, and rest. Object-pattern keys and member-pattern
    targets bind nothing here. -/
private partial def patternBoundNames : Pattern → List String
  | .identifier id => [id.name]
  | .objectPattern _ props => props.flatMap fun
      | .mk _ _ value _ _ => patternBoundNames value
      | .rest _ argument => patternBoundNames argument
  | .arrayPattern _ els => els.flatMap fun | some p => patternBoundNames p | none => []
  | .assignmentPattern _ left _ => patternBoundNames left
  | .restElement _ argument => patternBoundNames argument
  | .memberPattern _ _ _ _ => []

/-- Names a function parameter binds. -/
private def paramBoundNames : FunctionParam → List String
  | .simple id | .withDefault id _ | .rest id => [id.name]
  | .pattern pat => patternBoundNames pat

/-- Names a statement declares *directly* (not in nested blocks/functions):
    `let`/`const`/`var` declarators, a `function`/`class` declaration's own name.
    Used to pre-bind block-scoped names so references to them are not mistaken
    for free references. -/
private def declaredNamesStmt : Statement → List String
  | .variableDecl (.mk _ decls _) => decls.flatMap fun (.mk _ pat _ _) => patternBoundNames pat
  | .functionDecl _ id _ _ _ _ => [id.name]
  | .classDecl _ id .. => [id.name]
  | _ => []

/- Free variables of an expression/statement relative to `bound` — the
   identifiers genuinely *referenced* and not bound by an enclosing scope.
   Unlike `EscapeAnalysis.identsExpr`/`identsStmt` (which over-collect for a
   conservative escape analysis), this is scope-aware: it subtracts names bound
   by parameters, locals, loop/`catch` binders, excludes object-literal keys
   and non-computed member-property names, and never descends a name into a
   sibling scope. Used by TH0093 so a hoisted decl is flagged only when it
   makes a real free reference to a top-level mutated `let` (#91). -/
mutual
private partial def freeVarsExpr (bound : Std.HashSet String) : Expression → List String
  | .identifier _ n => if bound.contains n then [] else [n]
  | .literal _ _ _ | .thisExpr _ | .super_ _ | .metaProperty _ _ _
  | .patternExpr _ _ => []
  | .arrayExpr _ els => els.flatMap fun | some e => freeVarsExpr bound e | none => []
  | .objectExpr _ props => props.flatMap fun
      | .regular _ k v _ computed _ =>
          (if computed then freeVarsExpr bound k else []) ++ freeVarsExpr bound v
      | .spread _ a => freeVarsExpr bound a
  | .functionExpr _ id params body _ _ =>
      let bound := fvInsert bound ((id.map (·.name)).toList ++ params.flatMap paramBoundNames)
      freeVarsStmt bound body
  | .arrowFunctionExpr _ params body _ _ _ =>
      let bound := fvInsert bound (params.flatMap paramBoundNames)
      match body with | .inl e => freeVarsExpr bound e | .inr s => freeVarsStmt bound s
  | .unaryExpr _ _ _ a | .updateExpr _ _ a _ | .spreadElement _ a
  | .awaitExpr _ a | .chainExpr _ a => freeVarsExpr bound a
  | .binaryExpr _ _ l r | .assignmentExpr _ _ l r | .logicalExpr _ _ l r =>
      freeVarsExpr bound l ++ freeVarsExpr bound r
  | .memberExpr _ o p computed _ =>
      freeVarsExpr bound o ++ (if computed then freeVarsExpr bound p else [])
  | .privateMemberExpr _ o _ => freeVarsExpr bound o
  | .conditionalExpr _ t c a =>
      freeVarsExpr bound t ++ freeVarsExpr bound c ++ freeVarsExpr bound a
  | .callExpr _ f args _ | .newExpr _ f args =>
      freeVarsExpr bound f ++ args.flatMap (freeVarsExpr bound)
  | .sequenceExpr _ es => es.flatMap (freeVarsExpr bound)
  | .templateLiteral _ _ es => es.flatMap (freeVarsExpr bound)
  | .taggedTemplate _ t q => freeVarsExpr bound t ++ freeVarsExpr bound q
  | .classExpr .. => []
  | .yieldExpr _ a _ => match a with | some e => freeVarsExpr bound e | none => []

/-- Free variables of a statement list under block scoping: names declared
    directly in the list are bound for the whole list (matching lexical
    block/hoisting scope), then each statement is scanned. -/
private partial def freeVarsStmts (bound : Std.HashSet String)
    (stmts : List Statement) : List String :=
  let bound := fvInsert bound (stmts.flatMap declaredNamesStmt)
  stmts.flatMap (freeVarsStmt bound)

private partial def freeVarsStmt (bound : Std.HashSet String) : Statement → List String
  | .exprStmt _ e | .throwStmt _ e => freeVarsExpr bound e
  | .blockStmt _ b => freeVarsStmts bound b
  | .ifStmt _ t c a =>
      freeVarsExpr bound t ++ freeVarsStmt bound c
        ++ (match a with | some s => freeVarsStmt bound s | none => [])
  | .returnStmt _ a => match a with | some e => freeVarsExpr bound e | none => []
  | .variableDecl (.mk _ decls _) =>
      decls.flatMap fun (.mk _ _ init _) =>
        match init with | some e => freeVarsExpr bound e | none => []
  | .whileStmt _ t b => freeVarsExpr bound t ++ freeVarsStmt bound b
  | .doWhileStmt _ b t => freeVarsStmt bound b ++ freeVarsExpr bound t
  | .forStmt _ init t u b =>
      -- initializers are evaluated before the binders are in scope
      let initFv := match init with
        | some (.inl e) => freeVarsExpr bound e
        | some (.inr (.mk _ decls _)) =>
            decls.flatMap fun (.mk _ _ i _) =>
              match i with | some e => freeVarsExpr bound e | none => []
        | _ => []
      let bound := match init with
        | some (.inr (.mk _ decls _)) =>
            fvInsert bound (decls.flatMap fun (.mk _ pat _ _) => patternBoundNames pat)
        | _ => bound
      initFv ++ (match t with | some e => freeVarsExpr bound e | none => [])
        ++ (match u with | some e => freeVarsExpr bound e | none => []) ++ freeVarsStmt bound b
  | .forInStmt _ left r b | .forOfStmt _ left r b _ =>
      -- the iterable `r` is in the outer scope; only the body sees the binder
      let leftFv := match left with | .inl e => freeVarsExpr bound e | .inr _ => []
      let bodyBound := match left with
        | .inl _ => bound
        | .inr (.mk _ decls _) =>
            fvInsert bound (decls.flatMap fun (.mk _ pat _ _) => patternBoundNames pat)
      leftFv ++ freeVarsExpr bound r ++ freeVarsStmt bodyBound b
  | .switchStmt _ d cases =>
      freeVarsExpr bound d ++ cases.flatMap (fun (.mk _ t ss) =>
        (match t with | some e => freeVarsExpr bound e | none => [])
          ++ freeVarsStmts bound ss)
  | .tryStmt _ b h f =>
      freeVarsStmt bound b
        ++ (match h with
            | some (.mk _ param hb _) =>
                let bound := match param with
                  | some p => fvInsert bound (patternBoundNames p) | none => bound
                freeVarsStmt bound hb
            | none => [])
        ++ (match f with | some s => freeVarsStmt bound s | none => [])
  | .labeledStmt _ _ b | .withStmt _ _ b => freeVarsStmt bound b
  | .functionDecl _ id params body _ _ =>
      let bound := fvInsert bound (id.name :: params.flatMap paramBoundNames)
      freeVarsStmt bound body
  | _ => []
end

/-- A hoisted top-level declaration's source location and the free identifiers
    referenced by its body/initializer, or `none` if the item is not a hoisted
    declaration. A hoisted decl (`function`, or a `const`/`let` emitted as a
    top-level `def`) is elaborated OUTSIDE `main`, so any reference it makes to
    a top-level mutable `let` (a `main`-local `let mut`) is out of scope (#49).
    Free variables — not raw identifiers — so that parameters, locals,
    object-literal keys, and member-property names that merely share a name with
    a top-level mutable are not mistaken for references (#91). -/
private partial def hoistedRefs : TSStatement → Option (Option SourceLocation × List String)
  | .annotatedFuncDecl b _ _ params _ body _ _ _ _ =>
      some (b.loc, freeVarsStmt (fvInsert {} (params.map (·.1))) body)
  | .annotatedVarDecl b _ _ _ (some init) => some (b.loc, freeVarsExpr {} init)
  | .js (.classDecl b _ _ body ..) =>
      -- A v1 class lowers to hoisted decls (structure + namespace defs), so
      -- its ctor/method bodies are elaborated outside `main` like functions
      some (b.loc, body.flatMap fun el => match el with
        | .method (.mk _ _ (.functionExpr _ _ params mbody _ _) ..) =>
            freeVarsStmt (fvInsert {} (params.flatMap paramBoundNames)) mbody
        | .field (.mk _ _ (some init) ..) => freeVarsExpr {} init
        | _ => [])
  | .exportDecl _ inner => hoistedRefs inner
  | _ => none

/-- Method names declared by a top-level class (incl. export-wrapped) —
    the TH0102 name set. -/
private def classMethodNamesTS : TSStatement → List String
  | .js (.classDecl _ _ _ body ..) => body.filterMap fun
      | .method (.mk _ key _ .method false false none ..) => classKeyName? key
      | _ => none
  | .exportDecl _ inner => classMethodNamesTS inner
  | _ => []

/-- Member-property references of a TS statement (for the program-level
    TH0102 pass). -/
private def memberPropRefsTS : TSStatement → List MemberPropRef
  | .js s => memberPropRefsStmt s
  | .annotatedFuncDecl _ _ _ _ _ body _ _ _ _ => memberPropRefsStmt body
  | .annotatedVarDecl _ _ _ _ (some init) => memberPropRefsExpr false init
  | .exportDecl _ inner => memberPropRefsTS inner
  | _ => []

/-- Walk a TSProgram and return all Thales-subset violations (raw,
    without directive post-processing). -/
def subsetCheckRaw (prog : TSProgram) : Array Diagnostic :=
  let aliasEnv := buildAliasEnv prog.body
  let topRecvEnv := buildTopRecvEnv prog.body
  -- Module-level mutation/loop info over the reconstructed executable top-level
  -- block — the SAME block `buildModule` lowers into `main` (#49).
  let moduleInfo := EscapeAnalysis.analyze [] (.blockStmt {} (moduleExecutableStatements prog.body))
  -- TH0093: a hoisted declaration that reads a top-level mutated `let` would
  -- emit a `def` referencing a `main`-local binding — reject up front rather
  -- than emit uncompilable Lean.
  let th0093 : Array Diagnostic := prog.body.foldl (fun acc ts =>
    match hoistedRefs ts with
    | some (loc, refs) =>
        let refSet : Std.HashSet String := refs.foldl (·.insert ·) {}
        refSet.fold (fun a n =>
          if moduleInfo.mutated.contains n
          then a.push (mkThalesDiag (.topLevelMutableReferencedByHoisted n) loc)
          else a) acc
    | none => acc) #[]
  -- TH0102: a declared class-method name referenced outside direct-callee
  -- position, anywhere in the program (name-based over-approximation)
  let methodNameSet : Std.HashSet String :=
    prog.body.foldl (fun s ts => (classMethodNamesTS ts).foldl (·.insert ·) s) {}
  let th0102 : Array Diagnostic :=
    if methodNameSet.isEmpty then #[]
    else prog.body.foldl (fun acc ts =>
      (memberPropRefsTS ts).foldl (fun a r =>
        if !r.isDirectCallee && methodNameSet.contains r.prop then
          a.push (mkThalesDiag (.classMethodUsedAsValue r.prop) r.loc)
        else a) acc) #[]
  prog.body.foldl (fun acc ts =>
    acc ++ checkTSStmt aliasEnv topRecvEnv moduleInfo ts ++ checkTSStmtSwitch aliasEnv ts)
    (th0093 ++ th0102)

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
