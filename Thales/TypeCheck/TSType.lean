/-
  Thales/TypeCheck/TSType.lean
  TypeScript type representation
-/

namespace Thales.TypeCheck

/-- Numeric refinement-type kinds, forming an inclusion chain in `number`:
    `Bit ⊂ Byte ⊂ Natural ⊂ Integer ⊂ number`. Introduced via `@thales/prelude`. -/
inductive RefinementKind where
  | integer
  | natural
  | byte
  | bit
  deriving Repr, BEq, Inhabited

/-- The display name used in error messages and emit. -/
def RefinementKind.name : RefinementKind → String
  | .integer => "Integer"
  | .natural => "Natural"
  | .byte => "Byte"
  | .bit => "Bit"

/-- Chain rank: higher rank is more specific. `Bit` (3) ⊆ `Byte` (2) ⊆ `Natural` (1) ⊆ `Integer` (0). -/
def RefinementKind.rank : RefinementKind → Nat
  | .integer => 0
  | .natural => 1
  | .byte => 2
  | .bit => 3

/-- `a ⊆ b` in the refinement chain (lower-or-equal-rank ⊆ higher-rank, i.e. more specific ⊆ less specific). -/
def RefinementKind.le (a b : RefinementKind) : Bool :=
  b.rank ≤ a.rank

/-- Numeric range bounds for a refinement kind, as Floats.
    `Integer/Natural` use the IEEE-safe-integer bound 2^53 − 1. -/
def RefinementKind.bounds : RefinementKind → Option Float × Option Float
  | .integer => (some (-9007199254740991.0), some 9007199254740991.0)
  | .natural => (some 0.0, some 9007199254740991.0)
  | .byte => (some 0.0, some 255.0)
  | .bit => (some 0.0, some 1.0)

/-- Whether a `Float` literal is in-range and integral for the given refinement.
    `bit` requires the literal to be exactly 0 or 1; the others require an integer
    in-range. -/
def RefinementKind.literalInRange (k : RefinementKind) (lit : Float) : Bool :=
  let isIntegral : Bool := lit == lit.floor
  match k with
  | .integer => isIntegral && lit ≥ -9007199254740991.0 && lit ≤ 9007199254740991.0
  | .natural => isIntegral && lit ≥ 0.0 && lit ≤ 9007199254740991.0
  | .byte => isIntegral && lit ≥ 0.0 && lit ≤ 255.0
  | .bit => lit == 0.0 || lit == 1.0

mutual

/-- Core TypeScript type representation -/
inductive TSType where
  -- Primitives
  | number
  | string
  | boolean
  | bigint
  | symbol
  | void_
  | undefined
  | null_
  | never
  | unknown
  | any
  -- Refinement types: structurally `number`, tagged with a chain kind.
  -- See `RefinementKind` above and `Thales.TS.Runtime` for the runtime story.
  | refinement (kind : RefinementKind)
  -- Literal types
  | stringLit (s : String)
  | numberLit (n : Float)
  | booleanLit (b : Bool)
  -- Compound types
  | array (elem : TSType)
  | tuple (elements : List TSType)
  | object (members : List TSObjectMember)
  | function (params : List TSParamType) (ret : TSType)
  -- Set operations
  | union (types : List TSType)
  | intersection (types : List TSType)
  -- References (resolved during type checking)
  | ref (name : String) (typeArgs : List TSType)
  -- Type variables (allocated during generic checking, unique ID)
  -- constraint is stored here so call-site inference can check it
  | typeVar (id : Nat) (name : String) (constraint : Option TSType)
  -- Nullable/optional: T | null or T | undefined (emitted as Option T)
  | option (inner : TSType)
  -- Parenthesized (for parsing, normalized away later)
  | paren (inner : TSType)
  -- Conditional type: check extends extends_ ? trueType : falseType
  | conditional (check : TSType) (extends_ : TSType) (trueType : TSType) (falseType : TSType)
  -- Mapped type: { [keyVar in constraint]: valueType } with optional/readonly modifiers
  | mapped (keyVar : String) (constraint : TSType) (valueType : TSType)
           (optionalMod : Option Bool) (readonlyMod : Option Bool)

/-- Object type member -/
inductive TSObjectMember where
  | property (name : String) (type : TSType) (optional : Bool) (readonly : Bool)
  | method (name : String) (params : List TSParamType) (ret : TSType) (optional : Bool)
  | indexSignature (keyName : String) (keyType : TSType) (valueType : TSType) (readonly : Bool)

/-- Function parameter with type -/
inductive TSParamType where
  | mk (name : String) (type : TSType) (optional : Bool := false) (rest : Bool := false)

end

mutual
private partial def eqTSType (a b : TSType) : Bool :=
  match a, b with
  | .number, .number | .string, .string | .boolean, .boolean
  | .bigint, .bigint | .symbol, .symbol | .void_, .void_
  | .undefined, .undefined | .null_, .null_ | .never, .never
  | .unknown, .unknown | .any, .any => true
  | .refinement k1, .refinement k2 => k1 == k2
  | .stringLit s1, .stringLit s2 => s1 == s2
  | .numberLit n1, .numberLit n2 => n1 == n2
  | .booleanLit b1, .booleanLit b2 => b1 == b2
  | .array e1, .array e2 => eqTSType e1 e2
  | .option e1, .option e2 => eqTSType e1 e2
  | .tuple ts1, .tuple ts2 => ts1.length == ts2.length && (ts1.zip ts2).all (fun (x, y) => eqTSType x y)
  | .union ts1, .union ts2 => ts1.length == ts2.length && (ts1.zip ts2).all (fun (x, y) => eqTSType x y)
  | .intersection ts1, .intersection ts2 => ts1.length == ts2.length && (ts1.zip ts2).all (fun (x, y) => eqTSType x y)
  | .ref n1 args1, .ref n2 args2 => n1 == n2 && args1.length == args2.length && (args1.zip args2).all (fun (x, y) => eqTSType x y)
  | .typeVar id1 _ _, .typeVar id2 _ _ => id1 == id2
  | .paren t1, .paren t2 => eqTSType t1 t2
  | .function ps1 r1, .function ps2 r2 =>
    eqTSType r1 r2 && ps1.length == ps2.length &&
    (ps1.zip ps2).all (fun (p1, p2) => eqTSParamType p1 p2)
  | .object ms1, .object ms2 =>
    ms1.length == ms2.length && (ms1.zip ms2).all (fun (m1, m2) => eqTSObjectMember m1 m2)
  | .conditional c1 e1 t1 f1, .conditional c2 e2 t2 f2 =>
    eqTSType c1 c2 && eqTSType e1 e2 && eqTSType t1 t2 && eqTSType f1 f2
  | .mapped k1 c1 v1 o1 r1, .mapped k2 c2 v2 o2 r2 =>
    k1 == k2 && eqTSType c1 c2 && eqTSType v1 v2 && o1 == o2 && r1 == r2
  | _, _ => false
private partial def eqTSParamType (a b : TSParamType) : Bool :=
  match a, b with
  | .mk n1 t1 o1 r1, .mk n2 t2 o2 r2 => n1 == n2 && eqTSType t1 t2 && o1 == o2 && r1 == r2
private partial def eqTSObjectMember (a b : TSObjectMember) : Bool :=
  match a, b with
  | .property n1 t1 o1 r1, .property n2 t2 o2 r2 => n1 == n2 && eqTSType t1 t2 && o1 == o2 && r1 == r2
  | .method n1 ps1 r1 o1, .method n2 ps2 r2 o2 =>
    n1 == n2 && eqTSType r1 r2 && o1 == o2 && ps1.length == ps2.length &&
    (ps1.zip ps2).all (fun (p1, p2) => eqTSParamType p1 p2)
  | _, _ => false
end

instance : BEq TSType := ⟨eqTSType⟩
instance : Inhabited TSType := ⟨.any⟩
instance : Inhabited TSObjectMember := ⟨.property "" .any false false⟩
instance : Inhabited TSParamType := ⟨.mk "" .any⟩

/-- Normalize a union type to `TSType.option` if it is `T | null`, `T | undefined`,
    or `T | null | undefined`. Returns `none` if the union is not a nullable union. -/
def normalizeNullableUnion (types : List TSType) : Option TSType :=
  -- Separate null/undefined from other types
  let nullUndef := types.filter fun t => match t with | .null_ | .undefined => true | _ => false
  let nonNull := types.filter fun t => match t with | .null_ | .undefined => false | _ => true
  -- A nullable union has exactly one non-null member and at least one null/undefined
  match nonNull, nullUndef with
  | [inner], _ :: _ => some (.option inner)
  | _, _ => none

/-- Check if a TSType is a nullable type (i.e., `TSType.option T` or normalizable union). -/
def isNullable : TSType → Bool
  | .option _ => true
  | .union types => (normalizeNullableUnion types).isSome
  | _ => false

/-- Extract the inner type from an option/nullable type, if possible. -/
def optionInner : TSType → Option TSType
  | .option inner => some inner
  | .union types => match normalizeNullableUnion types with
    | some (.option inner) => some inner
    | _ => none
  | _ => none

/-- Generic type parameter: <T extends Foo = Bar> -/
structure TSTypeParam where
  name : String
  constraint : Option TSType := none
  default_ : Option TSType := none
  deriving Inhabited

/-- TypeScript type annotation -/
structure TypeAnnotation where
  type : TSType
  deriving Inhabited

end Thales.TypeCheck
