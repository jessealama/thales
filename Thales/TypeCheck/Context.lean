/-
  Thales/TypeCheck/Context.lean
  Type checking monad, context, and scope management
-/
import Thales.TypeCheck.TSType
import Thales.TypeCheck.TSAST
import Thales.TypeCheck.Diagnostic
import Std.Data.HashMap
import Std.Data.HashSet

namespace Thales.TypeCheck

open Thales.AST

/-- Type alias definition -/
structure TypeAliasDef where
  typeParams : List TSTypeParam
  body : TSType
  deriving Inhabited

/-- Interface definition -/
structure InterfaceDef where
  typeParams : List TSTypeParam
  members : List TSInterfaceMember
  deriving Inhabited

/-- A class's checkable surface: the instance object type plus the
    constructor signature (used by `new` for arity/argument checking). -/
structure ClassInfo where
  instanceType : TSType
  ctorParams : List (String × TSType)
  deriving Inhabited

/-- Mutable state accumulated during type checking -/
structure TypeCheckState where
  diagnostics : Array Diagnostic := #[]
  nextTypeVarId : Nat := 0
  assignedVars : Std.HashSet String := {}
  needsAssignmentCheck : Std.HashSet String := {}
  deriving Inhabited

/-- Read-only type context (per scope via ReaderT) -/
structure TypeContext where
  bindings : Std.HashMap String TSType := {}
  declaredTypes : Std.HashMap String TSType := {}  -- declared type (from annotation/inference)
  typeAliases : Std.HashMap String TypeAliasDef := {}
  interfaces : Std.HashMap String InterfaceDef := {}
  enums : Std.HashMap String TSType := {}
  classes : Std.HashMap String ClassInfo := {}  -- class name → instance type + ctor signature
  consts : Std.HashSet String := {}  -- names declared with `const` (for TS2588)
  returnType : Option TSType := none  -- expected return type in current function
  deriving Inhabited

/-- The type checking monad: pure, no IO -/
abbrev TypeCheckM := StateT TypeCheckState (ReaderT TypeContext Id)

/-- Emit a diagnostic -/
def emitDiagnostic (kind : DiagnosticKind) (loc : Option SourceLocation := none) : TypeCheckM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics.push { kind, location := loc } }

/-- Mark a variable as requiring definite assignment checking -/
def requireAssignmentCheck (name : String) : TypeCheckM Unit :=
  modify fun s => { s with needsAssignmentCheck := s.needsAssignmentCheck.insert name }

/-- Mark a variable as definitely assigned -/
def markAssigned (name : String) : TypeCheckM Unit :=
  modify fun s => { s with assignedVars := s.assignedVars.insert name }

/-- Check if a type includes undefined (directly or in a union) -/
private def includesUndefined (ty : TSType) : Bool :=
  match ty with
  | .undefined => true
  | .void_ => true
  | .union types => types.any fun t => match t with
    | .undefined | .void_ => true
    | _ => false
  | _ => false

/-- Check if a variable is definitely assigned; emit TS2454 if not.
    Skips checking for variables whose type includes undefined (tsc behavior). -/
def checkDefinitelyAssigned (name : String) (loc : Option SourceLocation := none) : TypeCheckM Unit := do
  let st ← get
  if st.needsAssignmentCheck.contains name && !st.assignedVars.contains name then
    -- Don't flag if the variable's type includes undefined (tsc doesn't flag these)
    let ctx ← read
    match ctx.bindings[name]? with
    | some ty => unless includesUndefined ty do
        emitDiagnostic (.variableUsedBeforeAssignment name) loc
    | none => emitDiagnostic (.variableUsedBeforeAssignment name) loc

/-- Snapshot current assignment state -/
def saveAssignmentState : TypeCheckM (Std.HashSet String) := do
  return (← get).assignedVars

/-- Restore assignment state -/
def restoreAssignmentState (saved : Std.HashSet String) : TypeCheckM Unit :=
  modify fun s => { s with assignedVars := saved }

/-- Intersect two assignment states (keep only vars assigned in BOTH) -/
def intersectAssigned (a b : Std.HashSet String) : Std.HashSet String :=
  a.fold (fun acc v => if b.contains v then acc.insert v else acc) {}

/-- Look up a variable binding in the current scope -/
def lookupBinding (name : String) : TypeCheckM (Option TSType) := do
  let ctx ← read
  return ctx.bindings[name]?

/-- Resolve a type alias by name -/
def resolveTypeAlias (name : String) : TypeCheckM (Option TSType) := do
  let ctx ← read
  return (ctx.typeAliases[name]?).map (·.body)

/-- Resolve a TSType, following type alias references -/
partial def resolveType (ty : TSType) : TypeCheckM TSType := do
  match ty with
  | .ref name [] =>
    let alias ← resolveTypeAlias name
    match alias with
    | some resolved => resolveType resolved
    | none =>
      -- Check if it's an enum
      let ctx ← read
      match ctx.enums[name]? with
      | some enumTy => return enumTy
      | none =>
        -- Check if it's a class
        match ctx.classes[name]? with
        | some info => return info.instanceType
        | none => return ty  -- unresolved ref, leave as-is
  | .paren inner => resolveType inner
  | .typeVar .. => return ty  -- don't resolve type variables
  | _ => return ty

/-- Run a computation with additional variable bindings (new scope) -/
def withScope {α : Type} (extraBindings : List (String × TSType)) (m : TypeCheckM α) : TypeCheckM α :=
  StateT.mk fun s =>
    ReaderT.mk fun ctx =>
      let newBindings := extraBindings.foldl (fun map (k, v) => map.insert k v) ctx.bindings
      (m.run s).run { ctx with bindings := newBindings }

/-- Run a computation with `name` marked as a `const` binding (for TS2588). -/
def withConst {α : Type} (name : String) (m : TypeCheckM α) : TypeCheckM α :=
  StateT.mk fun s =>
    ReaderT.mk fun ctx =>
      (m.run s).run { ctx with consts := ctx.consts.insert name }

/-- Look up whether `name` is bound as a `const` in the current scope chain. -/
def lookupConst (name : String) : TypeCheckM Bool := do
  return (← read).consts.contains name

/-- Run a computation with a new variable binding, setting both flow type and declared type -/
def withBinding {α : Type} (name : String) (declaredTy : TSType)
    (m : TypeCheckM α) : TypeCheckM α :=
  StateT.mk fun s =>
    ReaderT.mk fun ctx =>
      (m.run s).run { ctx with
        bindings := ctx.bindings.insert name declaredTy,
        declaredTypes := ctx.declaredTypes.insert name declaredTy }

/-- Run a computation with additional bindings, setting both flow and declared types -/
def withScopeAndDeclaredTypes {α : Type} (extraBindings : List (String × TSType))
    (m : TypeCheckM α) : TypeCheckM α :=
  StateT.mk fun s =>
    ReaderT.mk fun ctx =>
      let newBindings := extraBindings.foldl (fun map (k, v) => map.insert k v) ctx.bindings
      let newDeclared := extraBindings.foldl (fun map (k, v) => map.insert k v) ctx.declaredTypes
      (m.run s).run { ctx with bindings := newBindings, declaredTypes := newDeclared }

/-- Look up the declared type for a variable -/
def lookupDeclaredType (name : String) : TypeCheckM (Option TSType) := do
  return (← read).declaredTypes[name]?

/-- Run a computation in a function scope (with params and return type).
    Parameters seed both the flow type and the declared type — assignment
    checking and post-assignment flow updates (#24) treat parameters
    exactly like initialized `let` bindings. -/
def withFunctionScope {α : Type} (params : List (String × TSType)) (retTy : Option TSType)
    (m : TypeCheckM α) : TypeCheckM α :=
  StateT.mk fun s =>
    ReaderT.mk fun ctx =>
      let newBindings := params.foldl (fun map (k, v) => map.insert k v) ctx.bindings
      let newDeclared := params.foldl (fun map (k, v) => map.insert k v) ctx.declaredTypes
      (m.run s).run { ctx with bindings := newBindings, declaredTypes := newDeclared, returnType := retTy }

/-- Run a computation with a registered type alias -/
def withTypeAlias {α : Type} (name : String) (def_ : TypeAliasDef) (m : TypeCheckM α) : TypeCheckM α :=
  StateT.mk fun s =>
    ReaderT.mk fun ctx =>
      (m.run s).run { ctx with typeAliases := ctx.typeAliases.insert name def_ }

/-- Run a computation with a registered interface -/
def withInterface {α : Type} (name : String) (def_ : InterfaceDef) (m : TypeCheckM α) : TypeCheckM α :=
  StateT.mk fun s =>
    ReaderT.mk fun ctx =>
      (m.run s).run { ctx with interfaces := ctx.interfaces.insert name def_ }

/-- Run a computation with a registered enum binding -/
def withEnum {α : Type} (name : String) (ty : TSType) (m : TypeCheckM α) : TypeCheckM α :=
  StateT.mk fun s =>
    ReaderT.mk fun ctx =>
      let newCtx := { ctx with
        enums := ctx.enums.insert name ty
        bindings := ctx.bindings.insert name ty
      }
      (m.run s).run newCtx

/-- Run a computation with a registered class (instance type + ctor signature + class-name binding) -/
def withClass {α : Type} (name : String) (info : ClassInfo) (m : TypeCheckM α) : TypeCheckM α :=
  StateT.mk fun s =>
    ReaderT.mk fun ctx =>
      let newCtx := { ctx with
        classes := ctx.classes.insert name info
        bindings := ctx.bindings.insert name (.ref name [])
      }
      (m.run s).run newCtx

/-- Pure builder of a class's importable surface from a `classDecl`'s retained
    annotations (no body checking): fields become properties with their real
    readonly/optional flags, methods carry their annotated signatures, and
    ctor params come from the `.constructor` member. `.any` stands in for any
    missing annotation — the subset check owns rejection of those shapes. -/
def classInfoOfDecl : Statement → Option ClassInfo
  | .classDecl _ _ _ body .. => Id.run do
    let mut members : List TSObjectMember := []
    let mut ctorParams : List (String × TSType) := []
    for el in body do
      match el with
      | .field (.mk _ (.identifier _ fname) _ false false _ readonly optional typeAnnotation _) =>
        members := members ++ [.property fname (typeAnnotation.getD .any) optional readonly]
      | .method (.mk _ (.identifier _ mname) _ kind false static_ _ _ _ _ _ sigParams returnType) =>
        match kind with
        | .constructor =>
          ctorParams := sigParams.map fun (pname, ann, _, _) => (pname, ann.elim .any (·.type))
        | .method =>
          if !static_ then
            let ps := sigParams.map fun (pname, ann, opt, rest_) =>
              TSParamType.mk pname (ann.elim .any (·.type)) opt rest_
            members := members ++ [.method mname ps (returnType.elim .any (·.type)) false]
        | _ => pure ()  -- getters/setters: out of the v1 surface
      | _ => pure ()
    return some { instanceType := .object members, ctorParams }
  | _ => none

/-- Allocate a fresh type variable with a unique ID.
    Pass the constraint from the type parameter if any. -/
def freshTypeVar (name : String) (constraint : Option TSType) : TypeCheckM TSType := do
  let s ← get
  let id := s.nextTypeVarId
  set { s with nextTypeVarId := id + 1 }
  return .typeVar id name constraint

/-- Run the type checker and extract diagnostics -/
def runTypeCheckM (ctx : TypeContext) (m : TypeCheckM Unit) : Array Diagnostic :=
  let initState : TypeCheckState := {}
  let (_, finalState) := (m.run initState).run ctx
  finalState.diagnostics

/-- Run a value-producing TypeCheckM action and discard accumulated state. -/
def runTypeCheckMValue {α : Type} (ctx : TypeContext) (m : TypeCheckM α) : α :=
  let initState : TypeCheckState := {}
  let (val, _) := (m.run initState).run ctx
  val

end Thales.TypeCheck
