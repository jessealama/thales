/-
  Thales/TypeCheck/Narrowing.lean
  Control-flow narrowing: guard extraction, type narrowing, guard application.
  All functions are pure — no TypeCheckM dependency.
-/
import Thales.TypeCheck.TSType
import Thales.AST
import Std.Data.HashMap

namespace Thales.TypeCheck.Narrowing

open Thales.AST
open Thales.TypeCheck

inductive Guard where
  | typeofEquals (varName : String) (typeStr : String)
  | instanceOf (varName : String) (className : String)
  | equalsNull (varName : String)
  | equalsUndefined (varName : String)
  | truthy (varName : String)
  | discriminant (varName : String) (propName : String) (value : String)
  -- Refinement-type predicates: isInteger(x), isNatural(x), isByte(x),
  -- isBit(x), and Number.isSafeInteger(x) (treated as isInteger). True branch
  -- narrows the variable's type to the corresponding refinement.
  | refinementTest (varName : String) (kind : RefinementKind)
  | not (guard : Guard)
  | and (left : Guard) (right : Guard)
  | or (left : Guard) (right : Guard)
  deriving Inhabited

def matchesTypeof (ty : TSType) (typeStr : String) : Bool :=
  match typeStr with
  | "string" => match ty with | .string | .stringLit _ => true | _ => false
  | "number" => match ty with | .number | .numberLit _ => true | _ => false
  | "boolean" => match ty with | .boolean | .booleanLit _ => true | _ => false
  | "bigint" => match ty with | .bigint => true | _ => false
  | "symbol" => match ty with | .symbol => true | _ => false
  | "undefined" => match ty with | .undefined | .void_ => true | _ => false
  | "object" => match ty with | .null_ | .object _ | .array _ | .tuple _ | .ref _ _ => true | _ => false
  | "function" => match ty with | .function _ _ => true | _ => false
  | _ => false

def typeofToType (typeStr : String) : TSType :=
  match typeStr with
  | "string" => .string
  | "number" => .number
  | "boolean" => .boolean
  | "bigint" => .bigint
  | "symbol" => .symbol
  | "undefined" => .undefined
  | "object" => .object []
  | "function" => .function [] .any
  | _ => .any

def isFalsy (ty : TSType) : Bool :=
  match ty with
  | .null_ | .undefined => true
  | .booleanLit false => true
  | _ => false

/-- Check if a TSType is the null_ type -/
private def isNull : TSType → Bool
  | .null_ => true
  | _ => false

/-- Check if a TSType is the undefined type -/
private def isUndefined : TSType → Bool
  | .undefined => true
  | _ => false

/-- Check if an object type has a property with a given name and string literal value. -/
def hasLiteralProperty (ty : TSType) (propName : String) (value : String) : Bool :=
  match ty with
  | .object members =>
    members.any fun m => match m with
      | .property name (.stringLit s) _ _ => name == propName && s == value
      | _ => false
  | _ => false

/-! ## Guard extraction -/

partial def extractGuard : Expression → Option Guard
  -- Prelude refinement predicates `isInteger(x)`/`isNatural(x)`/`isByte(x)`/
  -- `isBit(x)` and `Number.isSafeInteger(x)` (treated as `isInteger`).
  -- Only bare-identifier arguments are recognized.
  | .callExpr _ (.identifier _ name) [.identifier _ varName] _ =>
    match RefinementKind.ofPredicate? name with
    | some kind => some (.refinementTest varName kind)
    | none => none
  | .callExpr _ (.memberExpr _ (.identifier _ "Number") (.identifier _ "isSafeInteger") false _)
              [.identifier _ varName] _ =>
    some (.refinementTest varName .integer)
  | .binaryExpr _ op left right =>
    match op with
    | .seq =>
      -- Helper: extract string value from literal or no-interpolation template literal
      let asString : Expression → Option String
        | .literal _ (.string s) _ => some s
        | .templateLiteral _ quasis exprs =>
          if exprs.isEmpty then
            match quasis with
            | [q] => some q.value
            | _ => none
          else none
        | _ => none
      match left, right with
      | .unaryExpr _ .typeof _ (.identifier _ varName), rhs =>
        match asString rhs with
        | some typeStr => some (.typeofEquals varName typeStr)
        | none => none
      | lhs, .unaryExpr _ .typeof _ (.identifier _ varName) =>
        match asString lhs with
        | some typeStr => some (.typeofEquals varName typeStr)
        | none => none
      | .identifier _ varName, .literal _ .null _ =>
        some (.equalsNull varName)
      | .literal _ .null _, .identifier _ varName =>
        some (.equalsNull varName)
      | .identifier _ varName, .identifier _ "undefined" =>
        if varName != "undefined" then some (.equalsUndefined varName) else none
      | .identifier _ "undefined", .identifier _ varName =>
        if varName != "undefined" then some (.equalsUndefined varName) else none
      -- x.prop === "value" (discriminant)
      | .memberExpr _ (.identifier _ varName) (.identifier _ propName) false _, .literal _ (.string value) _ =>
        some (.discriminant varName propName value)
      -- "value" === x.prop (commutative)
      | .literal _ (.string value) _, .memberExpr _ (.identifier _ varName) (.identifier _ propName) false _ =>
        some (.discriminant varName propName value)
      | _, _ => none
    | .sneq =>
      match left, right with
      | .unaryExpr _ .typeof _ (.identifier _ varName), .literal _ (.string typeStr) _ =>
        some (.not (.typeofEquals varName typeStr))
      | .literal _ (.string typeStr) _, .unaryExpr _ .typeof _ (.identifier _ varName) =>
        some (.not (.typeofEquals varName typeStr))
      | .identifier _ varName, .literal _ .null _ =>
        some (.not (.equalsNull varName))
      | .literal _ .null _, .identifier _ varName =>
        some (.not (.equalsNull varName))
      | .identifier _ varName, .identifier _ "undefined" =>
        if varName != "undefined" then some (.not (.equalsUndefined varName)) else none
      | .identifier _ "undefined", .identifier _ varName =>
        if varName != "undefined" then some (.not (.equalsUndefined varName)) else none
      -- x.prop !== "value"
      | .memberExpr _ (.identifier _ varName) (.identifier _ propName) false _, .literal _ (.string value) _ =>
        some (.not (.discriminant varName propName value))
      | .literal _ (.string value) _, .memberExpr _ (.identifier _ varName) (.identifier _ propName) false _ =>
        some (.not (.discriminant varName propName value))
      | _, _ => none
    | .instanceof =>
      match left, right with
      | .identifier _ varName, .identifier _ className =>
        some (.instanceOf varName className)
      | _, _ => none
    | _ => none
  | .logicalExpr _ op left right =>
    match op with
    | .and =>
      match extractGuard left, extractGuard right with
      | some g1, some g2 => some (.and g1 g2)
      | _, _ => none
    | .or =>
      match extractGuard left, extractGuard right with
      | some g1, some g2 => some (.or g1 g2)
      | _, _ => none
    | _ => none
  | .unaryExpr _ .not _ inner =>
    match extractGuard inner with
    | some g => some (.not g)
    | none => none
  | .identifier _ varName => some (.truthy varName)
  | _ => none

/-! ## Type narrowing -/

private def filterUnion (types : List TSType) (pred : TSType → Bool) : TSType :=
  let filtered := types.filter pred
  match filtered with
  | [] => .never
  | [single] => single
  | multiple => .union multiple

mutual

partial def narrowType (ty : TSType) (guard : Guard) : TSType :=
  match guard with
  -- Refinement-type predicate: in the true branch, narrow `number` (and
  -- supertypes) to the tested refinement. If the existing type is already a
  -- refinement, narrow to the meet (the smaller-rank kind).
  | .refinementTest _ kind =>
    let refTy : TSType := .refinement kind
    match ty with
    | .number | .any | .unknown => refTy
    | .refinement existing =>
      -- Meet: pick the more-specific (higher-rank) refinement.
      if existing.rank ≥ kind.rank then ty else refTy
    | .union types => filterUnion types fun t => match t with
        | .number | .refinement _ | .any | .unknown => true
        | _ => false
    | other => other  -- Don't change non-numeric types; predicate is vacuous.
  | .typeofEquals _ typeStr =>
    match ty with
    | .union types => filterUnion types (matchesTypeof · typeStr)
    | .any | .unknown => typeofToType typeStr
    | .typeVar id name constraint => .intersection [.typeVar id name constraint, typeofToType typeStr]
    | other => if matchesTypeof other typeStr then other else .never
  | .instanceOf _ className =>
    match ty with
    | .union types =>
      let filtered := types.filter fun t =>
        match t with
        | .ref name _ => name == className
        | .object _ | .any => true
        | _ => false
      match filtered with
      | [] => .ref className []
      | [single] => single
      | multiple => .union multiple
    | .any | .unknown => .ref className []
    | .typeVar id name constraint => .intersection [.typeVar id name constraint, .ref className []]
    | _ => .ref className []
  | .equalsNull _ =>
    match ty with
    | .union types => filterUnion types isNull
    | .option _ => .null_   -- narrowing Option T to null gives null_
    | .any | .unknown => .null_
    | .null_ => .null_
    | _ => .never
  | .equalsUndefined _ =>
    match ty with
    | .union types => filterUnion types isUndefined
    | .option _ => .null_   -- narrowing Option T to undefined gives null_ (same none branch)
    | .any | .unknown => .undefined
    | .undefined => .undefined
    | _ => .never
  | .truthy _ =>
    match ty with
    | .union types => filterUnion types (!isFalsy ·)
    | _ => if isFalsy ty then .never else ty
  | .discriminant _ propName value =>
    match ty with
    | .union types => filterUnion types (hasLiteralProperty · propName value)
    | _ => if hasLiteralProperty ty propName value then ty else .never
  | .not g => narrowTypeNeg ty g
  | .and g1 g2 => narrowType (narrowType ty g1) g2
  | .or g1 g2 =>
    let t1 := narrowType ty g1
    let t2 := narrowType ty g2
    match t1, t2 with
    | .never, other => other
    | other, .never => other
    | _, _ => .union [t1, t2]

partial def narrowTypeNeg (ty : TSType) (guard : Guard) : TSType :=
  match guard with
  -- Negated refinement predicate: nothing useful to conclude — the value
  -- could still be `number` or a different refinement, so leave it alone.
  | .refinementTest _ _ => ty
  | .typeofEquals _ typeStr =>
    match ty with
    | .union types => filterUnion types (!matchesTypeof · typeStr)
    | .any | .unknown => ty
    | _ => if matchesTypeof ty typeStr then .never else ty
  | .instanceOf _ className =>
    match ty with
    | .union types =>
      filterUnion types fun t =>
        match t with
        | .ref name _ => name != className
        | _ => true
    | _ => ty
  | .equalsNull _ =>
    match ty with
    | .union types => filterUnion types (!isNull ·)
    | .option inner => inner  -- narrowing Option T away from null gives T
    | .null_ => .never
    | _ => ty
  | .equalsUndefined _ =>
    match ty with
    | .union types => filterUnion types (!isUndefined ·)
    | .option inner => inner  -- narrowing Option T away from undefined gives T
    | .undefined => .never
    | _ => ty
  | .truthy _ =>
    match ty with
    | .union types => filterUnion types isFalsy
    | _ => if isFalsy ty then ty else .never
  | .discriminant _ propName value =>
    match ty with
    | .union types => filterUnion types (!hasLiteralProperty · propName value)
    | _ => if hasLiteralProperty ty propName value then .never else ty
  | .not g => narrowType ty g
  | .and g1 g2 =>
    let t1 := narrowTypeNeg ty g1
    let t2 := narrowTypeNeg ty g2
    match t1, t2 with
    | .never, other => other
    | other, .never => other
    | _, _ => .union [t1, t2]
  | .or g1 g2 =>
    narrowTypeNeg (narrowTypeNeg ty g1) g2

end

/-! ## Guard application -/

def guardVarNames : Guard → List String
  | .typeofEquals v _ | .instanceOf v _ | .equalsNull v | .equalsUndefined v | .truthy v | .discriminant v _ _ => [v]
  | .refinementTest v _ => [v]
  | .not g => guardVarNames g
  | .and g1 g2 | .or g1 g2 => guardVarNames g1 ++ guardVarNames g2

mutual

partial def applyGuard (guard : Guard) (bindings : Std.HashMap String TSType) : Std.HashMap String TSType :=
  match guard with
  | .and g1 g2 => applyGuard g2 (applyGuard g1 bindings)
  | .or g1 g2 =>
    let b1 := applyGuard g1 bindings
    let b2 := applyGuard g2 bindings
    let vars := (guardVarNames g1 ++ guardVarNames g2).eraseDups
    vars.foldl (fun acc varName =>
      let ty1 := (b1[varName]?).getD .never
      let ty2 := (b2[varName]?).getD .never
      let unified := match ty1, ty2 with
        | .never, other => other
        | other, .never => other
        | _, _ => .union [ty1, ty2]
      acc.insert varName unified
    ) bindings
  | .not g => applyNegatedGuard g bindings
  | guard =>
    let vars := guardVarNames guard
    vars.foldl (fun acc varName =>
      match acc[varName]? with
      | some ty => acc.insert varName (narrowType ty guard)
      | none => acc
    ) bindings

partial def applyNegatedGuard (guard : Guard) (bindings : Std.HashMap String TSType) : Std.HashMap String TSType :=
  match guard with
  | .and g1 g2 =>
    let b1 := applyNegatedGuard g1 bindings
    let b2 := applyNegatedGuard g2 bindings
    let vars := (guardVarNames g1 ++ guardVarNames g2).eraseDups
    vars.foldl (fun acc varName =>
      let ty1 := (b1[varName]?).getD .never
      let ty2 := (b2[varName]?).getD .never
      let unified := match ty1, ty2 with
        | .never, other => other
        | other, .never => other
        | _, _ => .union [ty1, ty2]
      acc.insert varName unified
    ) bindings
  | .or g1 g2 =>
    applyNegatedGuard g2 (applyNegatedGuard g1 bindings)
  | .not g => applyGuard g bindings
  | guard =>
    let vars := guardVarNames guard
    vars.foldl (fun acc varName =>
      match acc[varName]? with
      | some ty => acc.insert varName (narrowTypeNeg ty guard)
      | none => acc
    ) bindings

end

def bindingsDiff (newBindings _oldBindings : Std.HashMap String TSType) : List (String × TSType) :=
  newBindings.fold (fun acc name newTy =>
    acc ++ [(name, newTy)]
  ) []

/-! ## Switch statement support -/

/-- Classification of a switch discriminant expression. -/
inductive SwitchKind where
  | typeofVar (varName : String)
  | memberAccess (varName : String) (propName : String)
  | directVar (varName : String)
  | unknown
  deriving Inhabited

/-- Analyze a switch discriminant expression to determine what kind of narrowing applies. -/
def analyzeSwitchDiscriminant : Expression → SwitchKind
  | .unaryExpr _ .typeof _ (.identifier _ varName) => .typeofVar varName
  | .memberExpr _ (.identifier _ varName) (.identifier _ propName) false _ => .memberAccess varName propName
  | .identifier _ varName => .directVar varName
  | _ => .unknown

/-- Generate a guard for a switch case based on the switch kind and case test value. -/
def caseGuard (kind : SwitchKind) (testExpr : Expression) : Option Guard :=
  match kind with
  | .typeofVar varName =>
    match testExpr with
    | .literal _ (.string typeStr) _ => some (.typeofEquals varName typeStr)
    | _ => none
  | .memberAccess varName propName =>
    match testExpr with
    | .literal _ (.string value) _ => some (.discriminant varName propName value)
    | _ => none
  | .directVar varName =>
    match testExpr with
    | .literal _ .null _ => some (.equalsNull varName)
    | .identifier _ "undefined" => some (.equalsUndefined varName)
    | _ => none
  | .unknown => none

end Thales.TypeCheck.Narrowing
