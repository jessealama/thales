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

#eval testThalesReassignFormat
#eval testThalesLoopFormat
#eval testThalesCodeHelper
