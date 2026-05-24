/-
  Thales/TypeCheck/Generic.lean
  Type variable substitution and generic type argument inference
-/
import Thales.TypeCheck.TSType
import Thales.TypeCheck.Context
import Thales.TypeCheck.Diagnostic
import Thales.TypeCheck.TypeSubstitution
import Std.Data.HashMap

set_option autoImplicit false

namespace Thales.TypeCheck

open Thales.AST

/-! ## Type-argument inference (positional) -/

/-- Walk a parameter type and argument type in parallel, collecting typeVar bindings.
    When a typeVar is found in the param type, bind it to the corresponding
    piece of the arg type. First match wins (existing bindings are not overwritten). -/
partial def collectTypeVarBindings (paramTy argTy : TSType)
    (bindings : Std.HashMap Nat TSType) : Std.HashMap Nat TSType :=
  match paramTy with
  | .typeVar id _ _ =>
    if bindings.contains id then bindings
    else bindings.insert id argTy
  | .array elemParam =>
    match argTy with
    | .array elemArg => collectTypeVarBindings elemParam elemArg bindings
    -- A tuple literal [T1, T2, ...] can match T[]: infer T from element types
    | .tuple elems =>
      -- Widen stringLit/numberLit/booleanLit to their base types for homogeneous arrays
      let widenedElems := elems.map fun e => match e with
        | .stringLit _ => TSType.string
        | .numberLit _ => TSType.number
        | .booleanLit _ => TSType.boolean
        | other => other
      -- Use first element type (all same after widening for typical homogeneous arrays)
      let elemTy := widenedElems.headD TSType.any
      collectTypeVarBindings elemParam elemTy bindings
    | _ => bindings
  | .tuple paramElems =>
    match argTy with
    | .tuple argElems =>
      (paramElems.zip argElems).foldl
        (fun acc (pe, ae) => collectTypeVarBindings pe ae acc) bindings
    | _ => bindings
  | .function srcParams srcRet =>
    match argTy with
    | .function tgtParams tgtRet =>
      let bindings' := (srcParams.zip tgtParams).foldl
        (fun acc (srcP, tgtP) =>
          match srcP, tgtP with
          | .mk _ srcTy _ _, .mk _ tgtTy _ _ => collectTypeVarBindings srcTy tgtTy acc)
        bindings
      collectTypeVarBindings srcRet tgtRet bindings'
    | _ => bindings
  | .object paramMembers =>
    match argTy with
    | .object argMembers =>
      paramMembers.foldl (fun acc paramMember =>
        match paramMember with
        | .property name paramTy _ _ =>
          match argMembers.find? (fun m => match m with
            | .property n _ _ _ | .method n _ _ _ => n == name
            | .indexSignature _ _ _ _ => false) with
          | some (.property _ argMemberTy _ _) =>
            collectTypeVarBindings paramTy argMemberTy acc
          | some (.method _ argParams argRet _) =>
            collectTypeVarBindings paramTy (.function argParams argRet) acc
          | some (.indexSignature _ _ _ _) => acc
          | none => acc
        | .method name paramParams paramRet _ =>
          match argMembers.find? (fun m => match m with
            | .property n _ _ _ | .method n _ _ _ => n == name
            | .indexSignature _ _ _ _ => false) with
          | some (.method _ argParams argRet _) =>
            let acc' := (paramParams.zip argParams).foldl
              (fun a (pp, ap) => match pp, ap with
                | .mk _ pt _ _, .mk _ at_ _ _ => collectTypeVarBindings pt at_ a)
              acc
            collectTypeVarBindings paramRet argRet acc'
          | some (.property _ argTy _ _) =>
            collectTypeVarBindings (.function paramParams paramRet) argTy acc
          | some (.indexSignature _ _ _ _) => acc
          | none => acc
        | .indexSignature _ _ _ _ => acc
      ) bindings
    | _ => bindings
  | .conditional _ _ _ _ => bindings
  | .mapped _ _ _ _ _ => bindings
  -- Array<T> in extends pattern matches T[] argument
  | .ref "Array" [elemParam] =>
    match argTy with
    | .array elemArg => collectTypeVarBindings elemParam elemArg bindings
    | .ref "Array" [elemArg] => collectTypeVarBindings elemParam elemArg bindings
    | _ => bindings
  | _ => bindings

/-- Infer type arguments for a generic function call.
    Walks each (param type, arg type) pair and collects bindings.
    Fills in defaults for any unresolved type params. -/
def inferTypeArgs (typeParamIds : List (Nat × TSTypeParam))
    (paramTypes : List TSParamType) (argTypes : List TSType) :
    Std.HashMap Nat TSType :=
  -- Collect bindings from positional matching
  let bindings := (paramTypes.zip argTypes).foldl
    (fun acc (p, argTy) =>
      match p with
      | .mk _ paramTy _ _ => collectTypeVarBindings paramTy argTy acc)
    ({} : Std.HashMap Nat TSType)
  -- Fill in defaults for any unresolved type params
  typeParamIds.foldl (fun acc (id, param) =>
    if acc.contains id then acc
    else match param.default_ with
      | some defaultTy => acc.insert id defaultTy
      | none => acc  -- leave unresolved (will remain as typeVar)
  ) bindings

/-! ## Generic instantiation -/

/-- Allocate fresh type variables for a list of type parameters.
    Returns the (id, TSTypeParam) pairs and the allocated typeVar types. -/
def allocTypeVars (typeParams : List TSTypeParam) :
    TypeCheckM (List (Nat × TSTypeParam) × List TSType) := do
  let mut ids : List (Nat × TSTypeParam) := []
  let mut vars : List TSType := []
  for param in typeParams do
    let tv ← freshTypeVar param.name param.constraint
    match tv with
    | .typeVar id _ _ => ids := ids ++ [(id, param)]
    | _ => pure ()  -- shouldn't happen
    vars := vars ++ [tv]
  return (ids, vars)

/-- Instantiate a generic type alias with concrete type arguments.
    Returns the body type with type params substituted. -/
def instantiateTypeAlias (def_ : TypeAliasDef) (typeArgs : List TSType) :
    TypeCheckM TSType := do
  let (ids, _) ← allocTypeVars def_.typeParams
  -- First, replace all name-based refs in the body with typeVars
  let bodyWithVars := ids.foldl (fun body (id, param) =>
    replaceRefWithTypeVar body param.name id) def_.body
  -- Then build substitution: typeVar id → concrete type arg
  let bindings := (ids.zip typeArgs).foldl
    (fun acc ((id, _param), arg) => acc.insert id arg)
    ({} : Std.HashMap Nat TSType)
  return substitute bodyWithVars bindings

/-- Instantiate a generic interface with concrete type arguments.
    Returns the members with type params substituted. -/
def instantiateInterface (def_ : InterfaceDef) (typeArgs : List TSType) :
    TypeCheckM (List TSInterfaceMember) := do
  let (ids, _) ← allocTypeVars def_.typeParams
  let bindings := (ids.zip typeArgs).foldl
    (fun acc ((id, _param), arg) => acc.insert id arg)
    ({} : Std.HashMap Nat TSType)
  return def_.members.map fun member =>
    match member with
    | .property name ty opt ro =>
      let ty' := ids.foldl (fun t (id, param) => replaceRefWithTypeVar t param.name id) ty
      .property name (substitute ty' bindings) opt ro
    | .method name params retType opt =>
      let params' := params.map fun (.mk n t o r) =>
        let t' := ids.foldl (fun ty (id, param) => replaceRefWithTypeVar ty param.name id) t
        TSParamType.mk n (substitute t' bindings) o r
      let ret' := ids.foldl (fun t (id, param) => replaceRefWithTypeVar t param.name id) retType
      .method name params' (substitute ret' bindings) opt

/-- Compute keyof for an object type: union of string literal property names -/
def computeKeyof (ty : TSType) : TSType :=
  match ty with
  | .object members =>
    let names := members.filterMap fun
      | .property name _ _ _ => some (TSType.stringLit name)
      | .method name _ _ _ => some (TSType.stringLit name)
      | .indexSignature _ _ _ _ => none
    match names with
    | [] => .never
    | [single] => single
    | multiple => .union multiple
  | _ => .any

/-- Compute index access: look up property type by name -/
def computeIndexAccess (objTy : TSType) (key : String) : TSType :=
  match objTy with
  | .object members =>
    match members.find? (fun m => match m with
      | .property n _ _ _ | .method n _ _ _ => n == key
      | .indexSignature _ _ _ _ => false) with
    | some (.property _ ty _ _) => ty
    | some (.method _ params ret _) => .function params ret
    | some (.indexSignature _ _ _ _) => .any
    | none => .any
  | _ => .any

/-- Check if a type is .never -/
private def isNever : TSType → Bool
  | .never => true
  | _ => false

/-- Check if a type was a naked type parameter (bare typeVar or ref with no args).
    Used for distributive conditional type check. -/
private def isNakedTypeParam : TSType → Bool
  | .typeVar .. => true
  | .ref _ [] => true
  | _ => false

/-- Simplify a list of types into a union, filtering out .never -/
private def simplifyUnion (types : List TSType) : TSType :=
  let filtered := types.filter (!isNever ·)
  match filtered with
  | [] => .never
  | [single] => single
  | multiple => .union multiple

/-- Scan a TSType for typeVar nodes with IDs >= 9000 (infer placeholders).
    Returns list of (id, name) pairs. -/
private partial def collectInferVars : TSType → List (Nat × String)
  | .typeVar id name _ => if id >= 9000 then [(id, name)] else []
  | .option inner => collectInferVars inner
  | .array e => collectInferVars e
  | .tuple es => es.flatMap collectInferVars
  | .function ps r =>
    (ps.flatMap fun (.mk _ t _ _) => collectInferVars t) ++ collectInferVars r
  | .object ms => ms.flatMap fun
    | .property _ t _ _ => collectInferVars t
    | .method _ ps r _ =>
      (ps.flatMap fun (.mk _ t _ _) => collectInferVars t) ++ collectInferVars r
    | .indexSignature _ kt vt _ => collectInferVars kt ++ collectInferVars vt
  | .union ts => ts.flatMap collectInferVars
  | .intersection ts => ts.flatMap collectInferVars
  | .ref _ args => args.flatMap collectInferVars
  | .conditional c e t f =>
    collectInferVars c ++ collectInferVars e ++ collectInferVars t ++ collectInferVars f
  | .paren inner => collectInferVars inner
  | .mapped _ c v _ _ => collectInferVars c ++ collectInferVars v
  | _ => []

/-- Deduplicate a list of (Nat × String) pairs by Nat key -/
private def dedupByFst (xs : List (Nat × String)) : List (Nat × String) :=
  xs.foldl (fun acc pair =>
    if acc.any (fun p => p.1 == pair.1) then acc else acc ++ [pair]) []

/-- Replace placeholder infer var IDs with fresh unique IDs in both extends and true branch. -/
private def reallocateInferVars (extends_ trueType : TSType) :
    TypeCheckM (TSType × TSType) := do
  let inferVars := dedupByFst (collectInferVars extends_ ++ collectInferVars trueType)
  if inferVars.isEmpty then
    return (extends_, trueType)
  let mut idMap : Std.HashMap Nat TSType := {}
  for (oldId, name) in inferVars do
    let freshVar ← freshTypeVar name none
    idMap := idMap.insert oldId freshVar
  let extends_' := substitute extends_ idMap
  let trueType' := substitute trueType idMap
  return (extends_', trueType')

/-! ## extractKeys -/

/-- Extract string literal keys from a resolved type. -/
private def extractKeys : TSType → List String
  | .union types => types.filterMap fun t => match t with
    | .stringLit s => some s
    | _ => none
  | .stringLit s => [s]
  | _ => []

mutual

/-- Resolve a type, handling generic instantiation for .ref with type args.
    Use this instead of resolveType when generic types may appear.
    When a generic alias/interface is referenced without type args, defaults are filled in.
    Pass `loc` to emit TS2558 when the wrong number of type arguments is given. -/
partial def resolveTypeGeneric (ty : TSType) (loc : Option SourceLocation := none) :
    TypeCheckM TSType := do
  match ty with
  | .conditional check extends_ trueType falseType =>
    evaluateConditionalType check extends_ trueType falseType
  | .ref "__keyof" [innerTy] =>
    let resolved ← resolveTypeGeneric innerTy
    return computeKeyof resolved
  | .ref "__indexAccess" [objTy, .stringLit key] =>
    let resolved ← resolveTypeGeneric objTy
    return computeIndexAccess resolved key
  -- T[number] — element type of an array or tuple. Falls back to .any for
  -- non-array operands so we don't reject usages we simply can't model yet.
  | .ref "__indexAccess" [objTy, .number] =>
    let resolved ← resolveTypeGeneric objTy
    match resolved with
    | .array elem => return elem
    | .tuple [] => return .never
    | .tuple ts => return .union ts
    | _ => return .any
  -- typeof X (.Y)* — look up the qualified value name in the variable
  -- environment and return its type. Returns .any when the name is unknown
  -- or when the path has dots we can't resolve through the bindings map.
  | .ref "__typeof" [.ref name []] =>
    let ctx ← read
    match ctx.bindings[name]? with
    | some t => resolveTypeGeneric t loc
    | none => return .any
  | .ref name args =>
    let ctx ← read
    if args.isEmpty then
      -- No explicit type args: check if alias/interface is generic with defaults
      match ctx.typeAliases[name]? with
      | some aliasDef =>
        if aliasDef.typeParams.length > 0 then
          -- Fill in defaults for all type params (unresolved params left as .any)
          let defaultArgs := aliasDef.typeParams.map fun p =>
            p.default_.getD .any
          let instantiated ← instantiateTypeAlias aliasDef defaultArgs
          resolveTypeGeneric instantiated loc
        else
          -- Resolve alias body through resolveTypeGeneric to handle __keyof, __indexAccess, etc.
          resolveTypeGeneric aliasDef.body loc
      | none =>
        match ctx.interfaces[name]? with
        | some ifaceDef =>
          if ifaceDef.typeParams.length > 0 then
            let defaultArgs := ifaceDef.typeParams.map fun p =>
              p.default_.getD .any
            let ifaceMembers ← instantiateInterface ifaceDef defaultArgs
            let objMembers := ifaceMembers.map fun m =>
              match m with
              | .property n t o r => TSObjectMember.property n t o r
              | .method n ps ret o => TSObjectMember.method n ps ret o
            return .object objMembers
          else
            -- Non-generic interface: expand to object type
            let objMembers := ifaceDef.members.map fun m =>
              match m with
              | .property n t o r => TSObjectMember.property n t o r
              | .method n ps ret o => TSObjectMember.method n ps ret o
            return .object objMembers
        | none => resolveType ty
    else
      -- Has explicit type args: instantiate with them, checking count
      match ctx.typeAliases[name]? with
      | some aliasDef =>
        if aliasDef.typeParams.length > 0 then
          -- Validate argument count; emit diagnostic for too many args
          if args.length > aliasDef.typeParams.length then
            emitDiagnostic (.wrongTypeArgCount name aliasDef.typeParams.length args.length) loc
          let instantiated ← instantiateTypeAlias aliasDef (args.take aliasDef.typeParams.length)
          resolveTypeGeneric instantiated loc
        else
          resolveType (.ref name [])
      | none =>
        match ctx.interfaces[name]? with
        | some ifaceDef =>
          if ifaceDef.typeParams.length > 0 then
            -- Validate argument count; emit diagnostic for too many args
            if args.length > ifaceDef.typeParams.length then
              emitDiagnostic (.wrongTypeArgCount name ifaceDef.typeParams.length args.length) loc
            let safeArgs := args.take ifaceDef.typeParams.length
            let ifaceMembers ← instantiateInterface ifaceDef safeArgs
            let objMembers := ifaceMembers.map fun m =>
              match m with
              | .property n t o r => TSObjectMember.property n t o r
              | .method n ps ret o => TSObjectMember.method n ps ret o
            return .object objMembers
          else
            return ty
        | none => return ty
  | .mapped keyVar constraint valueType optMod roMod =>
    evaluateMappedType keyVar constraint valueType optMod roMod
  | .paren inner => resolveTypeGeneric inner loc
  | .typeVar .. => return ty
  -- Normalize nullable unions T | null / T | undefined to TSType.option T
  | .union types =>
    match normalizeNullableUnion types with
    | some optTy => return optTy
    | none => resolveType ty
  | .option inner =>
    let inner' ← resolveTypeGeneric inner loc
    return .option inner'
  | _ => resolveType ty

/-- Check if type `a` is a subtype of (assignable to) type `b`.
    Primitives, any, unknown, never, literal widening, structural object/function subtyping. -/
partial def isSubtype (a b : TSType) : TypeCheckM Bool := do
  -- Short-circuit: same named ref is always assignable to itself
  if let (.ref n1 [], .ref n2 []) := (a, b) then
    if n1 == n2 then return true
  -- Enum branding: when target is an enum ref, only accept same enum ref or any/never/typeVar
  let ctx ← read
  if let .ref bName [] := b then
    if ctx.enums.contains bName then
      match a with
      | .ref aName [] => return aName == bName
      | .any | .never => return true
      | .typeVar .. => return true
      | _ => return false
  -- Resolve type aliases before comparing (use resolveTypeGeneric to handle generic refs)
  let a ← resolveTypeGeneric a
  let b ← resolveTypeGeneric b
  -- Infer variables (ID >= 9000) act as wildcards: anything is assignable to them
  if let .typeVar id _ _ := b then
    if id >= 9000 then return true
  match a, b with
  -- Refinement chain: Bit ⊆ Byte ⊆ Natural ⊆ Integer ⊆ number
  -- (See `RefinementKind.le` in `TSType.lean`.)
  | .refinement k1, .refinement k2 => return k1.le k2
  -- Refinements widen to plain `number`.
  | .refinement _, .number => return true
  -- A literal numeric value is assignable to a refinement when it satisfies the
  -- refinement's range/integrality predicate.
  | .numberLit n, .refinement k => return k.literalInRange n
  -- Same type (identity)
  | .number, .number => return true
  | .string, .string => return true
  | .boolean, .boolean => return true
  | .bigint, .bigint => return true
  | .symbol, .symbol => return true
  | .void_, .void_ => return true
  | .null_, .null_ => return true
  | .undefined, .undefined => return true
  | .never, .never => return true
  | .unknown, .unknown => return true
  | .any, .any => return true
  -- any is both top and bottom (intentionally unsound, matching tsc)
  | .any, _ => return true
  | _, .any => return true
  -- unknown is top (supertype of everything)
  | _, .unknown => return true
  -- never is bottom (subtype of everything)
  | .never, _ => return true
  -- Literal types widen to their base type
  | .numberLit _, .number => return true
  | .stringLit _, .string => return true
  | .booleanLit _, .boolean => return true
  -- Same literal values
  | .numberLit n1, .numberLit n2 => return n1 == n2
  | .stringLit s1, .stringLit s2 => return s1 == s2
  | .booleanLit b1, .booleanLit b2 => return b1 == b2
  -- void_ accepts undefined
  | .undefined, .void_ => return true
  -- Union on the right: A <: (B | C) iff A <: B or A <: C
  | _, .union types => types.anyM (isSubtype a ·)
  -- Union on the left: (A | B) <: C iff A <: C and B <: C
  | .union types, _ => types.allM (isSubtype · b)
  -- Intersection on the left: (A & B) <: C iff A <: C or B <: C
  | .intersection types, _ => types.anyM (isSubtype · b)
  -- Intersection on the right: A <: (B & C) iff A <: B and A <: C
  | _, .intersection types => types.allM (isSubtype a ·)
  -- Option subtyping: Option T <: Option U iff T <: U
  | .option t1, .option t2 => isSubtype t1 t2
  -- Option T is a supertype of T (some) and null_/undefined (none)
  | .null_, .option _ => return true
  | .undefined, .option _ => return true
  | t, .option u => isSubtype t u  -- T <: Option T (allows returning T where Option T expected)
  -- Array subtyping (covariant for now)
  | .array e1, .array e2 => isSubtype e1 e2
  -- Array<T> is equivalent to T[] for subtyping with infer
  | .array e1, .ref "Array" [e2] => isSubtype e1 e2
  | .ref "Array" [e1], .array e2 => isSubtype e1 e2
  | .ref "Array" [e1], .ref "Array" [e2] => isSubtype e1 e2
  -- Tuple subtyping: same length, element-wise covariant
  | .tuple src, .tuple tgt =>
    if src.length != tgt.length then return false
    (src.zip tgt).allM (fun (s, t) => isSubtype s t)
  -- Tuple is assignable to an array of the union of its element types
  | .tuple elems, .array elemTy =>
    elems.allM (isSubtype · elemTy)
  -- Object structural subtyping: source must have all required target members
  | .object srcMembers, .object tgtMembers =>
    tgtMembers.allM fun tgtMember =>
      match tgtMember with
      | .property name tgtTy optional _ =>
        match srcMembers.find? (fun m => match m with
          | .property n _ _ _ | .method n _ _ _ => n == name
          | .indexSignature _ _ _ _ => false) with
        | some (.property _ srcTy _ _) => isSubtype srcTy tgtTy
        | some (.method _ params ret _) => isSubtype (.function params ret) tgtTy
        | some (.indexSignature _ _ _ _) => return false
        | none => return optional  -- missing optional property is OK
      | .method name tgtParams tgtRet _ =>
        match srcMembers.find? (fun m => match m with
          | .property n _ _ _ | .method n _ _ _ => n == name
          | .indexSignature _ _ _ _ => false) with
        | some (.method _ srcParams srcRet _) =>
          isSubtype (.function srcParams srcRet) (.function tgtParams tgtRet)
        | some (.property _ srcTy _ _) =>
          isSubtype srcTy (.function tgtParams tgtRet)
        | some (.indexSignature _ _ _ _) => return false
        | none => return false
      | .indexSignature _ _ _ _ => return true  -- index signature subtyping deferred
  -- Function subtyping: params contravariant, return covariant
  | .function srcParams srcRet, .function tgtParams tgtRet => do
    -- Check return type (covariant)
    let retOk ← isSubtype srcRet tgtRet
    if !retOk then return false
    -- Check param types (contravariant: target param <: source param)
    -- If target has a rest ...args: any[] parameter, skip all param checks (wildcard)
    let hasAnyRestParam := tgtParams.any fun (.mk _ ty _ isRest) =>
      isRest && (match ty with | .any => true | .array .any => true | _ => false)
    if !hasAnyRestParam then
      for i in [:tgtParams.length] do
        if i < srcParams.length then
          let (.mk _ srcTy _ _) := srcParams[i]!
          let (.mk _ tgtTy _ _) := tgtParams[i]!
          let paramOk ← isSubtype tgtTy srcTy  -- contravariant!
          if !paramOk then return false
    return true
  -- Type variables: same ID is assignable to itself; infer vars (id >= 9000) are wildcards
  | .typeVar id1 _ _, .typeVar id2 _ _ => return id1 == id2 || id2 >= 9000
  -- Type variable ↔ unresolved ref with same name (parser produces .ref, checker produces .typeVar)
  | .typeVar _ n1 _, .ref n2 [] => return n1 == n2
  | .ref n1 [], .typeVar _ n2 _ => return n1 == n2
  -- Unresolved refs: same name is compatible
  | .ref n1 _, .ref n2 _ => return n1 == n2
  -- Base type assignable to literal union (our synthesis doesn't always produce literals)
  | .number, .numberLit _ => return true
  | .string, .stringLit _ => return true
  | .boolean, .booleanLit _ => return true
  -- Conditional types: resolve then compare
  | .conditional .., _ => do
    let resolved ← resolveTypeGeneric a
    isSubtype resolved b
  | _, .conditional .. => do
    let resolved ← resolveTypeGeneric b
    isSubtype a resolved
  -- Mapped types: resolve then compare
  | .mapped .., _ => do
    let resolved ← resolveTypeGeneric a
    isSubtype resolved b
  | _, .mapped .. => do
    let resolved ← resolveTypeGeneric b
    isSubtype a resolved
  -- Default: not a subtype
  | _, _ => return false

/-- Evaluate a single conditional type check (no distribution). -/
partial def evaluateSingleConditional (resolvedCheck extends_ trueType falseType : TSType) :
    TypeCheckM TSType := do
  let ok ← isSubtype resolvedCheck extends_
  if ok then
    let idBindings := collectTypeVarBindings extends_ resolvedCheck {}
    -- Substitute typeVar ids (for typeVar nodes) and ref names (for infer var ref nodes)
    let nameBindings := buildInferNameBindings extends_ idBindings
    let result := substituteInferRefs (substitute trueType idBindings) nameBindings
    resolveTypeGeneric result
  else
    resolveTypeGeneric falseType

/-- Evaluate a conditional type, handling distribution over unions.
    Distribution occurs when the resolved check type is a union AND the original
    check (before resolution) was a naked type variable (not wrapped in [], {}, etc.).
    After type argument substitution, a naked type param T becomes the substituted type
    directly; a wrapped [T] becomes [substituted]. So we distribute when originalCheck
    is either a typeVar OR the resolved check is a union that came from direct substitution
    (indicated by originalCheck being a union itself or a typeVar). -/
partial def evaluateConditionalType (originalCheck extends_ trueType falseType : TSType) :
    TypeCheckM TSType := do
  -- Note: infer variables in extends_ have IDs >= 9000 (placeholder IDs from the parser).
  -- We keep these IDs intact so that isSubtype can treat them as wildcards.
  let resolvedCheck ← resolveTypeGeneric originalCheck
  match resolvedCheck with
  | .union members =>
    -- Distribute if:
    -- 1. originalCheck is a typeVar (pre-substitution naked param)
    -- 2. originalCheck is itself a union (post-substitution naked param T → A|B)
    -- Don't distribute if originalCheck is wrapped (tuple, array, etc.)
    let shouldDistribute := isNakedTypeParam originalCheck || (match originalCheck with
      | .union _ => true
      | _ => false)
    if shouldDistribute then
      let mut results : List TSType := []
      for member in members do
        -- For distribution, substitute the current member for any occurrence of
        -- originalCheck in trueType/falseType (these were substituted from T → union,
        -- so we need to "re-substitute" with the per-member type).
        let trueM := substituteType trueType originalCheck member
        let falseM := substituteType falseType originalCheck member
        let result ← evaluateSingleConditional member extends_ trueM falseM
        results := results ++ [result]
      return simplifyUnion results
    else
      evaluateSingleConditional resolvedCheck extends_ trueType falseType
  | _ =>
    evaluateSingleConditional resolvedCheck extends_ trueType falseType

/-- Evaluate a mapped type by iterating over keys and building object members. -/
partial def evaluateMappedType (keyVar : String) (constraint valueType : TSType)
    (optMod roMod : Option Bool) : TypeCheckM TSType := do
  let resolvedConstraint ← resolveTypeGeneric constraint
  let keys := extractKeys resolvedConstraint
  let mut members : List TSObjectMember := []
  for key in keys do
    let substituted := substituteRef valueType keyVar (.stringLit key)
    let resolved ← resolveTypeGeneric substituted
    let optional := match optMod with
      | some true => true
      | some false => false
      | none => false
    let readonly := match roMod with
      | some true => true
      | some false => false
      | none => false
    members := members ++ [.property key resolved optional readonly]
  return .object members

end

end Thales.TypeCheck
