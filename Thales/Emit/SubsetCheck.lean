/-
  Thales/Emit/SubsetCheck.lean
  Enforces the Thales-TS v1 subset. Returns TH#### diagnostics for
  any construct outside the subset. Assumes type checking has already
  succeeded; operates on the typed AST.
-/
import Thales.TypeCheck.TSAST
import Thales.TypeCheck.Diagnostic
import Thales.Emit.DirectiveApply
import Std.Data.HashMap

namespace Thales.Emit

open Thales.AST
open Thales.TypeCheck

/-- Environment for switch exhaustiveness checking.
    aliasEnv maps type alias names to their resolved TSType.
    bindingEnv maps identifier names to their declared TSType. -/
structure SwitchEnv where
  aliasEnv   : Std.HashMap String TSType := {}
  bindingEnv : Std.HashMap String TSType := {}

/-- Method names that mutate their receiver. -/
private def mutatingMethodNames : List String :=
  ["push", "pop", "shift", "unshift", "splice", "sort", "reverse",
   "fill", "copyWithin", "set", "delete", "clear", "add"]

/-- Build a Diagnostic for a ThalesKind at the given optional location. -/
private def mkThalesDiag (kind : ThalesKind) (loc : Option SourceLocation) : Diagnostic :=
  { kind := .thales kind, location := loc }

mutual

/-- Check an expression for mutation violations. -/
partial def checkExpr (expr : Expression) : Array Diagnostic :=
  match expr with
  | .assignmentExpr b _ left right =>
    let loc := b.loc
    let targetDiags : Array Diagnostic :=
      match left with
      | .identifier _ name =>
        #[mkThalesDiag (.cannotReassignVariable name) loc]
      | .memberExpr _ _ _ computed _ =>
        if computed then
          #[mkThalesDiag .cannotAssignArrayElement loc]
        else
          #[mkThalesDiag .cannotAssignObjectProperty loc]
      | _ => #[]
    targetDiags ++ checkExpr right
  | .updateExpr b _ argument _ =>
    let loc := b.loc
    let targetDiags : Array Diagnostic :=
      match argument with
      | .identifier _ name =>
        #[mkThalesDiag (.cannotReassignVariable name) loc]
      | _ => #[]
    targetDiags ++ checkExpr argument
  | .callExpr b callee arguments _ =>
    let loc := b.loc
    let calleeDiags : Array Diagnostic :=
      match callee with
      | .memberExpr _ obj (.identifier _ propName) false _ =>
        if mutatingMethodNames.elem propName then
          #[mkThalesDiag (.cannotCallMutatingMethod propName) loc]
            ++ checkExpr obj
        else
          checkExpr callee
      | _ => checkExpr callee
    calleeDiags ++ (arguments.foldl (fun acc arg => acc ++ checkExpr arg) #[])
  | .unaryExpr _ _ _ argument =>
    checkExpr argument
  | .binaryExpr _ _ left right =>
    checkExpr left ++ checkExpr right
  | .logicalExpr _ _ left right =>
    checkExpr left ++ checkExpr right
  | .memberExpr _ obj prop _ _ =>
    checkExpr obj ++ checkExpr prop
  | .privateMemberExpr _ obj _ =>
    checkExpr obj
  | .conditionalExpr _ test consequent alternate =>
    checkExpr test ++ checkExpr consequent ++ checkExpr alternate
  | .newExpr _ callee arguments =>
    checkExpr callee ++ (arguments.foldl (fun acc arg => acc ++ checkExpr arg) #[])
  | .chainExpr _ inner =>
    checkExpr inner
  | .sequenceExpr _ exprs =>
    exprs.foldl (fun acc e => acc ++ checkExpr e) #[]
  | .templateLiteral _ _ exprs =>
    exprs.foldl (fun acc e => acc ++ checkExpr e) #[]
  | .taggedTemplate _ tag quasi =>
    checkExpr tag ++ checkExpr quasi
  | .arrayExpr _ elements =>
    elements.foldl (fun acc optE =>
      match optE with
      | some e => acc ++ checkExpr e
      | none => acc) #[]
  | .objectExpr _ props =>
    props.foldl (fun acc p =>
      match p with
      | .regular _ _ v _ _ _ => acc ++ checkExpr v
      | .spread _ arg => acc ++ checkExpr arg) #[]
  -- TH0012: async function expressions — emit diagnostic, still recurse body
  | .functionExpr b _ _ body _ async =>
    (if async then #[mkThalesDiag .asyncNotSupported b.loc] else #[])
      ++ checkStmt body
  -- TH0012: async arrow functions — emit diagnostic, still recurse body
  | .arrowFunctionExpr b _ body _ async _ =>
    let bodyDiags : Array Diagnostic :=
      match body with
      | .inl e => checkExpr e
      | .inr s => checkStmt s
    (if async then #[mkThalesDiag .asyncNotSupported b.loc] else #[])
      ++ bodyDiags
  | .spreadElement _ arg =>
    checkExpr arg
  | .yieldExpr _ arg _ =>
    match arg with
    | some e => checkExpr e
    | none => #[]
  -- TH0012: await expression — emit diagnostic, still recurse argument
  | .awaitExpr b arg =>
    #[mkThalesDiag .asyncNotSupported b.loc] ++ checkExpr arg
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

/-- Check a statement for subset violations (mutation + control-flow). -/
partial def checkStmt (stmt : Statement) : Array Diagnostic :=
  match stmt with
  | .emptyStmt _ => #[]
  | .debuggerStmt _ => #[]
  | .exprStmt _ expr =>
    checkExpr expr
  | .blockStmt _ body =>
    body.foldl (fun acc s => acc ++ checkStmt s) #[]
  | .ifStmt _ test consequent alternate =>
    checkExpr test
      ++ checkStmt consequent
      ++ (match alternate with | some s => checkStmt s | none => #[])
  -- TH0010: loop statements — emit once, do NOT recurse into body
  | .whileStmt b _ _ =>
    #[mkThalesDiag .loopNotSupported b.loc]
  | .doWhileStmt b _ _ =>
    #[mkThalesDiag .loopNotSupported b.loc]
  | .forStmt b _ _ _ _ =>
    #[mkThalesDiag .loopNotSupported b.loc]
  | .forInStmt b _ _ _ =>
    #[mkThalesDiag .loopNotSupported b.loc]
  | .forOfStmt b _ _ _ _ =>
    #[mkThalesDiag .loopNotSupported b.loc]
  | .breakStmt _ _ => #[]
  | .continueStmt _ _ => #[]
  | .returnStmt _ arg =>
    match arg with
    | some e => checkExpr e
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
    nonRecord ++ checkExpr arg
  -- Untyped `catch (e)` is the standard TS form (tsc rejects `catch (e: E)`
  -- with TS1196); thales infers the catch type from the try-body's Except.
  | .tryStmt _ block handler _ =>
    let blockDiags := checkStmt block
    let handlerDiags := match handler with
      | some (CatchClause.mk _ _ handlerBody _) => checkStmt handlerBody
      | none => #[]
    blockDiags ++ handlerDiags
  | .switchStmt _ discriminant cases =>
    checkExpr discriminant
      ++ cases.foldl (fun acc (SwitchCase.mk _ _ stmts) =>
           stmts.foldl (fun acc2 s => acc2 ++ checkStmt s) acc) #[]
  | .labeledStmt _ _ body =>
    checkStmt body
  | .withStmt _ obj body =>
    checkExpr obj ++ checkStmt body
  | .variableDecl (VariableDeclaration.mk _ decls _) =>
    decls.foldl (fun acc (VariableDeclarator.mk _ _ initOpt _) =>
      match initOpt with
      | some e => acc ++ checkExpr e
      | none => acc) #[]
  -- TH0012: async function declarations — emit diagnostic, still recurse body
  | .functionDecl b _ _ body _ async =>
    (if async then #[mkThalesDiag .asyncNotSupported b.loc] else #[])
      ++ checkStmt body
  -- TH0030: class declarations — emit diagnostic, optionally TH0031 for extends, do NOT recurse
  | .classDecl b _ superClass _ =>
    let baseDiag := #[mkThalesDiag .classNotSupported b.loc]
    match superClass with
    | some _ => baseDiag ++ #[mkThalesDiag .inheritanceNotSupported b.loc]
    | none => baseDiag

/-- Check class elements for mutation violations. -/
partial def checkClassElements (elements : List ClassElement) : Array Diagnostic :=
  elements.foldl (fun acc elem =>
    match elem with
    | .method (MethodDefinition.mk _ key value _ _ _ ..) =>
      acc ++ checkExpr key ++ checkExpr value
    | .field (FieldDefinition.mk _ key valueOpt _ _ ..) =>
      acc ++ checkExpr key ++ (match valueOpt with | some v => checkExpr v | none => #[])
    | .staticBlock _ body =>
      body.foldl (fun acc2 s => acc2 ++ checkStmt s) acc) #[]

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

/-- Check a single switch statement for TH0040 exhaustiveness.
    Returns a diagnostic if the switch on a discriminated union is non-exhaustive. -/
private def checkSwitchExhaustive
    (env : SwitchEnv) (loc : Option SourceLocation)
    (discriminant : Expression) (cases : List SwitchCase) : Option Diagnostic :=
  -- Pattern: switch (ident.field) where computed=false
  match discriminant with
  | .memberExpr _ (.identifier _ scrutName) (.identifier _ fieldName) false _ =>
    -- Look up the type of scrutName in the binding environment
    match env.bindingEnv.get? scrutName with
    | none => none
    | some rawTy =>
      -- Resolve through aliases
      let resolvedTy := resolveType env.aliasEnv rawTy
      match resolvedTy with
      | .union branches =>
        -- Get discriminator info
        match discriminatorInfo branches with
        | none => none
        | some (discField, expectedLiterals) =>
          -- The switch must be on the discriminator field
          if discField != fieldName then none
          else
            -- Check for a default arm (exhaustive by definition)
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
      | _ => none
  | _ => none

/-- Walk a statement body checking for switch exhaustiveness violations.
    Uses the provided SwitchEnv for identifier lookups. -/
partial def checkSwitchStmt (env : SwitchEnv) (stmt : Statement) : Array Diagnostic :=
  match stmt with
  | .blockStmt _ body =>
    body.foldl (fun acc s => acc ++ checkSwitchStmt env s) #[]
  | .ifStmt _ _ consequent alternate =>
    checkSwitchStmt env consequent
      ++ (match alternate with | some s => checkSwitchStmt env s | none => #[])
  | .switchStmt b discriminant cases =>
    let switchDiag : Array Diagnostic :=
      match checkSwitchExhaustive env b.loc discriminant cases with
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
  | .js s => checkStmt s
  | .annotatedVarDecl b _ _ typeAnn initOpt =>
    checkAnn b.loc typeAnn
      ++ (match initOpt with
          | some e => checkExpr e
          | none => #[])
  -- TH0012: async annotated function declarations — emit diagnostic, still recurse body.
  -- TH0060 is no longer SubsetCheck's responsibility, so no suppression filter is needed.
  | .annotatedFuncDecl b _ _ params returnType body _ async _throwsAnn _ =>
    let paramTypeDiags := params.foldl (fun acc (_, ann, _, _) =>
      acc ++ checkAnn b.loc ann) #[]
    let bodyDiags := checkStmt body
    (if async then #[mkThalesDiag .asyncNotSupported b.loc] else #[])
      ++ paramTypeDiags
      ++ checkAnn b.loc returnType
      ++ bodyDiags
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

/-- Check a TS-level statement for switch exhaustiveness (TH0040).
    Requires a SwitchEnv with type alias and binding information. -/
def checkTSStmtSwitch (aliasEnv : Std.HashMap String TSType) (ts : TSStatement)
    : Array Diagnostic :=
  match ts with
  | .annotatedFuncDecl _ _ _ params _ body _ _ _ _ =>
    let bindingEnv := buildParamEnv params
    let env : SwitchEnv := { aliasEnv, bindingEnv }
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
