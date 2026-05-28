/-
  Test/TypeCheck/AssignTargetTest.lean
  Unit tests for classifyAssignTarget.
-/
import Thales.TypeCheck.AssignTarget
import Thales.TypeCheck.Context
import Thales.TypeCheck.TypedExpression
import Thales.AST

open Thales.TypeCheck
open Thales.AST

/-- Build a no-loc identifier expression. -/
private def idExpr (name : String) : Expression :=
  .identifier {} name

/-- Build a no-loc number literal. -/
private def numLit (n : Float) : Expression :=
  .literal {} (.number n) (toString n)

/-- Build a no-loc string literal. -/
private def strLit (s : String) : Expression :=
  .literal {} (.string s) s!"\"{s}\""

/-- A stub synth: always return a typed expression with the given type
    and an empty children array, sufficient for classifier tests. -/
private def stubSynth (ty : TSType) : Expression → TypeCheckM TypedExpression :=
  fun e => pure { expr := .js e, type := ty, children := #[] }

/-- An enum-shaped object type with one readonly member `B`. -/
private def enumObjTy : TSType :=
  .object [.property "B" (.ref "ENUM1" []) false true]

/-- A non-readonly interface shape with one writable member `p`. -/
private def writableObjTy : TSType :=
  .object [.property "p" .number false false]

/-- Run a TypeCheckM with a single const `x` registered. -/
private def runWithConst {α : Type} (m : TypeCheckM α) : α :=
  let emptyConsts : Std.HashSet String := {}
  let ctx : TypeContext := { consts := emptyConsts.insert "x" }
  runTypeCheckMValue ctx m

/-- Run a TypeCheckM with no extras. -/
private def runPlain {α : Type} (m : TypeCheckM α) : α :=
  runTypeCheckMValue {} m

def testConstIdentifierIsTS2588 : IO Unit := do
  let result := runWithConst <| classifyAssignTarget (stubSynth .any) (idExpr "x")
  match result with
  | some (.cannotAssignToConstant "x") => pure ()
  | _ => throw (IO.userError "expected TS2588 for const x")

def testLetIdentifierIsNone : IO Unit := do
  let result := runPlain <| classifyAssignTarget (stubSynth .any) (idExpr "y")
  unless result.isNone do
    throw (IO.userError "expected none for non-const id")

def testEnumDotMemberIsTS2540 : IO Unit := do
  let obj := idExpr "ENUM1"
  let mem : Expression := .memberExpr {} obj (.identifier {} "B") false
  let result := runPlain <| classifyAssignTarget (stubSynth enumObjTy) mem
  match result with
  | some (.cannotAssignToReadOnlyProperty "B") => pure ()
  | _ => throw (IO.userError "expected TS2540 for ENUM1.B")

def testEnumBracketStringKeyIsTS2540 : IO Unit := do
  let obj := idExpr "ENUM1"
  let mem : Expression := .memberExpr {} obj (strLit "B") true
  let result := runPlain <| classifyAssignTarget (stubSynth enumObjTy) mem
  match result with
  | some (.cannotAssignToReadOnlyProperty "B") => pure ()
  | _ => throw (IO.userError "expected TS2540 for ENUM1[\"B\"]")

def testWritableInterfacePropIsNone : IO Unit := do
  let obj := idExpr "i"
  let mem : Expression := .memberExpr {} obj (.identifier {} "p") false
  let result := runPlain <| classifyAssignTarget (stubSynth writableObjTy) mem
  unless result.isNone do
    throw (IO.userError "expected none for writable prop")

def testUnionWithOneWritableIsNone : IO Unit := do
  let obj := idExpr "u"
  let mem : Expression := .memberExpr {} obj (.identifier {} "p") false
  let unionTy : TSType := .union [
    .object [.property "p" .number false true],
    .object [.property "p" .number false false],
  ]
  let result := runPlain <| classifyAssignTarget (stubSynth unionTy) mem
  unless result.isNone do
    throw (IO.userError "expected none for partly-writable union")

def testUnionAllReadonlyIsTS2540 : IO Unit := do
  let obj := idExpr "u"
  let mem : Expression := .memberExpr {} obj (.identifier {} "p") false
  let unionTy : TSType := .union [
    .object [.property "p" .number false true],
    .object [.property "p" .number false true],
  ]
  let result := runPlain <| classifyAssignTarget (stubSynth unionTy) mem
  match result with
  | some (.cannotAssignToReadOnlyProperty "p") => pure ()
  | _ => throw (IO.userError "expected TS2540 for fully-readonly union")

def testLiteralLHSIsTS2364 : IO Unit := do
  let result := runPlain <| classifyAssignTarget (stubSynth .any) (numLit 1.0)
  match result with
  | some .invalidAssignmentTarget => pure ()
  | _ => throw (IO.userError "expected TS2364 for literal LHS")

def testCallLHSIsTS2364 : IO Unit := do
  let callExpr : Expression := .callExpr {} (idExpr "f") []
  let result := runPlain <| classifyAssignTarget (stubSynth .any) callExpr
  match result with
  | some .invalidAssignmentTarget => pure ()
  | _ => throw (IO.userError "expected TS2364 for call LHS")

#eval testConstIdentifierIsTS2588
#eval testLetIdentifierIsNone
#eval testEnumDotMemberIsTS2540
#eval testEnumBracketStringKeyIsTS2540
#eval testWritableInterfacePropIsNone
#eval testUnionWithOneWritableIsNone
#eval testUnionAllReadonlyIsTS2540
#eval testLiteralLHSIsTS2364
#eval testCallLHSIsTS2364
