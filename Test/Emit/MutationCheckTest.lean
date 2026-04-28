/-
  Test/Emit/MutationCheckTest.lean
  Verifies TH0001-TH0005 are emitted for mutation patterns.
-/
import Thales.Emit.SubsetCheck
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser
open Thales.TypeCheck

/-- Helper: parse a TS source string, run subsetCheck, check for a code. -/
def expectCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    unless diags.any (·.thalesCode? = some code) do
      let formatted := (diags.map (·.format "test.ts")).toList
      throw (IO.userError s!"expected TH{code}, got: {formatted}")

def testReassignment : IO Unit := expectCode "let x = 0; x = 1;" 1
def testCompoundAssignment : IO Unit := expectCode "let x = 0; x += 1;" 1
def testIncrement : IO Unit := expectCode "let x = 0; x++;" 1
def testDecrement : IO Unit := expectCode "let x = 0; --x;" 1
def testArrayIndexWrite : IO Unit := expectCode "const arr = [1]; arr[0] = 2;" 2
def testPropertyWrite : IO Unit := expectCode "const o = {x: 1}; o.x = 2;" 3
def testPushMethodCall : IO Unit := expectCode "const arr = [1]; arr.push(2);" 4
def testSortMethodCall : IO Unit := expectCode "const arr = [1]; arr.sort();" 4

/-- Closure capture: outer let, inner arrow reassigns it.
    For v1, treat this as TH0001 (reassignment detection fires inside the closure body);
    if the implementation specifically detects capture, TH0005 is also acceptable. -/
def testCapturedWrite : IO Unit := do
  let src := "let counter = 0; const bump = () => { counter = counter + 1; };"
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    -- Accept either TH0001 or TH0005; the spirit is "mutation inside a closure is caught".
    unless diags.any (fun d => d.thalesCode? = some 1 || d.thalesCode? = some 5) do
      throw (IO.userError s!"expected TH0001 or TH0005; got {(diags.map (·.format "")).toList}")

#eval testReassignment
#eval testCompoundAssignment
#eval testIncrement
#eval testDecrement
#eval testArrayIndexWrite
#eval testPropertyWrite
#eval testPushMethodCall
#eval testSortMethodCall
#eval testCapturedWrite
