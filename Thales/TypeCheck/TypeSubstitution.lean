/-
  Thales/TypeCheck/TypeSubstitution.lean
  Pure structural substitution operations on `TSType`.

  Every function in this module is a total/partial pure transformation
  `TSType → … → TSType`. There is no monad, no diagnostic emission, no
  cross-recursion into the type-checker's resolution or subtyping cycle.
  Callers in `Generic.lean` (the mutual core) and elsewhere import this
  module by name; the helpers used to live inside the big mutual block
  only because they sat near their callers, not because of any cyclic
  dependency.
-/
import Thales.AST
import Thales.TypeCheck.TSType
import Std.Data.HashMap

set_option autoImplicit false

namespace Thales.TypeCheck

open Thales.AST

/-- Replace every `.ref refName []` in `ty` with `.typeVar varId refName constraint`.
    Used when lifting a name-based generic alias body into an internal
    typeVar-keyed representation prior to substitution. -/
partial def replaceRefWithTypeVar (ty : TSType) (refName : String) (varId : Nat)
    (constraint : Option TSType := none) : TSType :=
  match ty with
  | .ref name [] => if name == refName then .typeVar varId refName constraint else ty
  | .ref name args => .ref name (args.map (replaceRefWithTypeVar · refName varId constraint))
  | .option inner => .option (replaceRefWithTypeVar inner refName varId constraint)
  | .array elem => .array (replaceRefWithTypeVar elem refName varId constraint)
  | .tuple elems => .tuple (elems.map (replaceRefWithTypeVar · refName varId constraint))
  | .object members => .object (members.map fun m =>
      match m with
      | .property n t o r => .property n (replaceRefWithTypeVar t refName varId constraint) o r
      | .method n ps ret o =>
        .method n
          (ps.map fun (.mk pn pt po pr) =>
            .mk pn (replaceRefWithTypeVar pt refName varId constraint) po pr)
          (replaceRefWithTypeVar ret refName varId constraint) o
      | .indexSignature kn kt vt ro =>
        .indexSignature kn (replaceRefWithTypeVar kt refName varId constraint)
          (replaceRefWithTypeVar vt refName varId constraint) ro)
  | .function params ret =>
    .function
      (params.map fun (.mk n t o r) =>
        .mk n (replaceRefWithTypeVar t refName varId constraint) o r)
      (replaceRefWithTypeVar ret refName varId constraint)
  | .union types => .union (types.map (replaceRefWithTypeVar · refName varId constraint))
  | .intersection types => .intersection (types.map (replaceRefWithTypeVar · refName varId constraint))
  | .paren inner => replaceRefWithTypeVar inner refName varId constraint
  | .conditional c e t f =>
    .conditional
      (replaceRefWithTypeVar c refName varId constraint)
      (replaceRefWithTypeVar e refName varId constraint)
      (replaceRefWithTypeVar t refName varId constraint)
      (replaceRefWithTypeVar f refName varId constraint)
  | .mapped k c v o r =>
    .mapped k (replaceRefWithTypeVar c refName varId constraint) (replaceRefWithTypeVar v refName varId constraint) o r
  | other => other

/-! ## Substitute typeVar IDs -/

mutual

/-- Substitute type variables in a TSType according to a bindings map. -/
partial def substitute (ty : TSType) (bindings : Std.HashMap Nat TSType) : TSType :=
  match ty with
  | .typeVar id _ _ => (bindings[id]?).getD ty
  | .option inner => .option (substitute inner bindings)
  | .array elem => .array (substitute elem bindings)
  | .tuple elems => .tuple (elems.map (substitute · bindings))
  | .object members => .object (members.map (substituteObjectMember · bindings))
  | .function params ret =>
    .function (params.map (substituteParam · bindings)) (substitute ret bindings)
  | .union types => .union (types.map (substitute · bindings))
  | .intersection types => .intersection (types.map (substitute · bindings))
  | .ref name args => .ref name (args.map (substitute · bindings))
  | .paren inner => substitute inner bindings
  | .conditional c e t f =>
    .conditional (substitute c bindings) (substitute e bindings) (substitute t bindings) (substitute f bindings)
  | .mapped k c v o r =>
    .mapped k (substitute c bindings) (substitute v bindings) o r
  | other => other  -- primitives, literals pass through unchanged

/-- Substitute in object member types. -/
partial def substituteObjectMember (m : TSObjectMember) (bindings : Std.HashMap Nat TSType) :
    TSObjectMember :=
  match m with
  | .property name ty opt ro => .property name (substitute ty bindings) opt ro
  | .method name params ret opt =>
    .method name (params.map (substituteParam · bindings)) (substitute ret bindings) opt
  | .indexSignature keyName keyType valueType ro =>
    .indexSignature keyName (substitute keyType bindings) (substitute valueType bindings) ro

/-- Substitute in function parameter types. -/
partial def substituteParam (p : TSParamType) (bindings : Std.HashMap Nat TSType) : TSParamType :=
  match p with
  | .mk name ty opt rest => .mk name (substitute ty bindings) opt rest

end

/-! ## substituteRef -/

/-- Replace all occurrences of `.ref name []` with `replacement`.
    Used for mapped-type key-variable substitution. -/
partial def substituteRef (ty : TSType) (name : String) (replacement : TSType) : TSType :=
  match ty with
  | .ref n args =>
    if n == name && args.isEmpty then replacement
    else .ref n (args.map (substituteRef · name replacement))
  | .option inner => .option (substituteRef inner name replacement)
  | .array e => .array (substituteRef e name replacement)
  | .tuple es => .tuple (es.map (substituteRef · name replacement))
  | .function ps r =>
    .function (ps.map fun (.mk pn pt po pr) => .mk pn (substituteRef pt name replacement) po pr)
      (substituteRef r name replacement)
  | .object ms => .object (ms.map fun m => match m with
    | .property n t o ro => .property n (substituteRef t name replacement) o ro
    | .method n ps ret o =>
      .method n (ps.map fun (.mk pn pt po pr) => .mk pn (substituteRef pt name replacement) po pr)
        (substituteRef ret name replacement) o
    | .indexSignature kn kt vt ro =>
      .indexSignature kn (substituteRef kt name replacement) (substituteRef vt name replacement) ro)
  | .union ts => .union (ts.map (substituteRef · name replacement))
  | .intersection ts => .intersection (ts.map (substituteRef · name replacement))
  | .conditional c e t f =>
    .conditional (substituteRef c name replacement) (substituteRef e name replacement)
      (substituteRef t name replacement) (substituteRef f name replacement)
  | .mapped k c v o r =>
    if k == name then .mapped k (substituteRef c name replacement) v o r
    else .mapped k (substituteRef c name replacement) (substituteRef v name replacement) o r
  | .paren inner => substituteRef inner name replacement
  | other => other

/-! ## Helpers previously inside the big mutual block (purely structural) -/

/-- Replace every structural occurrence of `from_` with `to_` in `ty`.
    Used for per-member substitution during conditional type distribution. -/
partial def substituteType (ty from_ to_ : TSType) : TSType :=
  if ty == from_ then to_
  else match ty with
  | .option inner => .option (substituteType inner from_ to_)
  | .array elem => .array (substituteType elem from_ to_)
  | .tuple elems => .tuple (elems.map (substituteType · from_ to_))
  | .function params ret =>
    .function (params.map fun (.mk n t o r) => .mk n (substituteType t from_ to_) o r)
              (substituteType ret from_ to_)
  | .union types => .union (types.map (substituteType · from_ to_))
  | .intersection types => .intersection (types.map (substituteType · from_ to_))
  | .object members => .object (members.map fun m =>
      match m with
      | .property n t o r => .property n (substituteType t from_ to_) o r
      | .method n ps ret o =>
        .method n (ps.map fun (.mk pn pt po pr) => .mk pn (substituteType pt from_ to_) po pr)
               (substituteType ret from_ to_) o
      | .indexSignature kn kt vt ro =>
        .indexSignature kn (substituteType kt from_ to_) (substituteType vt from_ to_) ro)
  | .conditional c e t f =>
    .conditional (substituteType c from_ to_) (substituteType e from_ to_)
                 (substituteType t from_ to_) (substituteType f from_ to_)
  | .ref n args => .ref n (args.map (substituteType · from_ to_))
  | other => other

/-- Build a name → bound-type mapping for infer variables found in `extends_`.
    Infer variables appear as `.typeVar id name _` with id >= 9000 in the extends
    pattern. After collectTypeVarBindings the bindings map is id → concrete type;
    this function turns that into (name, concrete type) pairs for ref substitution. -/
partial def buildInferNameBindings (extends_ : TSType)
    (idBindings : Std.HashMap Nat TSType) : List (String × TSType) :=
  match extends_ with
  | .typeVar id name _ =>
    if id >= 9000 then
      match idBindings[id]? with
      | some ty => [(name, ty)]
      | none => []
    else []
  | .array elem => buildInferNameBindings elem idBindings
  | .tuple elems =>
    elems.flatMap (buildInferNameBindings · idBindings)
  | .function params ret =>
    (params.flatMap fun (.mk _ t _ _) => buildInferNameBindings t idBindings)
    ++ buildInferNameBindings ret idBindings
  | .union types =>
    types.flatMap (buildInferNameBindings · idBindings)
  | .intersection types =>
    types.flatMap (buildInferNameBindings · idBindings)
  | .ref _ args =>
    args.flatMap (buildInferNameBindings · idBindings)
  | _ => []

/-- Substitute `.ref "Name" []` nodes that correspond to infer-variable names. -/
partial def substituteInferRefs (ty : TSType) (nameBindings : List (String × TSType)) : TSType :=
  match ty with
  | .ref name [] =>
    match nameBindings.find? (fun (n, _) => n == name) with
    | some (_, bound) => bound
    | none => ty
  | .ref name args => .ref name (args.map (substituteInferRefs · nameBindings))
  | .array elem => .array (substituteInferRefs elem nameBindings)
  | .tuple elems => .tuple (elems.map (substituteInferRefs · nameBindings))
  | .function params ret =>
    .function (params.map fun (.mk n t o r) => .mk n (substituteInferRefs t nameBindings) o r)
              (substituteInferRefs ret nameBindings)
  | .union types => .union (types.map (substituteInferRefs · nameBindings))
  | .intersection types => .intersection (types.map (substituteInferRefs · nameBindings))
  | .conditional c e t f =>
    .conditional (substituteInferRefs c nameBindings) (substituteInferRefs e nameBindings)
                 (substituteInferRefs t nameBindings) (substituteInferRefs f nameBindings)
  | .object members => .object (members.map fun m =>
      match m with
      | .property n t o r => .property n (substituteInferRefs t nameBindings) o r
      | .method n ps ret o =>
        .method n (ps.map fun (.mk pn pt po pr) => .mk pn (substituteInferRefs pt nameBindings) po pr)
               (substituteInferRefs ret nameBindings) o
      | .indexSignature kn kt vt ro =>
        .indexSignature kn (substituteInferRefs kt nameBindings) (substituteInferRefs vt nameBindings) ro)
  | other => other

end Thales.TypeCheck
