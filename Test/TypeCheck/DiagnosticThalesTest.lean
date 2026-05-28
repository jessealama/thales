/-
  Test/TypeCheck/DiagnosticThalesTest.lean
  Validates TH#### diagnostic formatting.
-/
import Thales.TypeCheck.Diagnostic
import Thales.AST

open Thales.TypeCheck
open Thales.AST

/-- TH0001 with a variable name formats with zero-padded code. -/
def testThalesReassignFormat : IO Unit := do
  let loc : SourceLocation := {
    start := { line := 1, column := 0 }
    «end» := { line := 1, column := 4 }
  }
  let d : Diagnostic := {
    kind := .thales (.cannotReassignVariable "x")
    location := some loc
  }
  let got := d.format "foo.ts"
  let want := "foo.ts(1,1): error TH0001: Cannot reassign variable 'x'"
  unless got == want do
    throw (IO.userError s!"\nwant: {want}\ngot:  {got}")

/-- TH0010 (loop) formats without a captured name. -/
def testThalesLoopFormat : IO Unit := do
  let loc : SourceLocation := {
    start := { line := 3, column := 1 }
    «end» := { line := 5, column := 0 }
  }
  let d : Diagnostic := {
    kind := .thales .loopNotSupported
    location := some loc
  }
  let got := d.format "bar.ts"
  let want := "bar.ts(3,2): error TH0010: Loop not supported; use recursion or array methods"
  unless got == want do
    throw (IO.userError s!"\nwant: {want}\ngot:  {got}")

/-- thalesCode? extracts the numeric code for a Thales-category diagnostic. -/
def testThalesCodeHelper : IO Unit := do
  let d : Diagnostic := {
    kind := .thales (.cannotAssignArrayElement)
    location := none
  }
  unless d.thalesCode? = some 2 do
    throw (IO.userError s!"expected some 2, got {repr d.thalesCode?}")
  let dTsc : Diagnostic := {
    kind := .identifierNotFound "foo"
    location := none
  }
  unless dTsc.thalesCode? = none do
    throw (IO.userError "expected none for TS diagnostic")

/-- TS2588 formats with the offending name. -/
def testCannotAssignToConstantFormat : IO Unit := do
  let loc : SourceLocation := {
    start := { line := 2, column := 0 }
    «end» := { line := 2, column := 1 }
  }
  let d : Diagnostic := {
    kind := .cannotAssignToConstant "x"
    location := some loc
  }
  let got := d.format "foo.ts"
  let want := "foo.ts(2,1): error TS2588: Cannot assign to 'x' because it is a constant"
  unless got == want do
    throw (IO.userError s!"\nwant: {want}\ngot:  {got}")

/-- TS2540 formats with the offending property name. -/
def testCannotAssignToReadOnlyPropertyFormat : IO Unit := do
  let loc : SourceLocation := {
    start := { line := 3, column := 0 }
    «end» := { line := 3, column := 1 }
  }
  let d : Diagnostic := {
    kind := .cannotAssignToReadOnlyProperty "B"
    location := some loc
  }
  let got := d.format "foo.ts"
  let want := "foo.ts(3,1): error TS2540: Cannot assign to 'B' because it is a read-only property"
  unless got == want do
    throw (IO.userError s!"\nwant: {want}\ngot:  {got}")

/-- TS2364 has fixed wording. -/
def testInvalidAssignmentTargetFormat : IO Unit := do
  let loc : SourceLocation := {
    start := { line := 4, column := 0 }
    «end» := { line := 4, column := 1 }
  }
  let d : Diagnostic := {
    kind := .invalidAssignmentTarget
    location := some loc
  }
  let got := d.format "foo.ts"
  let want := "foo.ts(4,1): error TS2364: The left-hand side of an assignment expression must be a variable or a property access"
  unless got == want do
    throw (IO.userError s!"\nwant: {want}\ngot:  {got}")

#eval testThalesReassignFormat
#eval testThalesLoopFormat
#eval testThalesCodeHelper
#eval testCannotAssignToConstantFormat
#eval testCannotAssignToReadOnlyPropertyFormat
#eval testInvalidAssignmentTargetFormat
