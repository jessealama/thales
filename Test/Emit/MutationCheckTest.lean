/-
  Test/Emit/MutationCheckTest.lean
  Verifies the #24 mutation routing: TH0001 (still-rejected forms),
  TH0002-TH0004 (member/method mutation), TH0005 (captured), TH0006
  (expression position), TH0007 (throws/try context).
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

/-- Helper: assert that NO diagnostic with the given TH code fires. -/
def expectNoCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    if diags.any (·.thalesCode? = some code) then
      let formatted := (diags.map (·.format "test.ts")).toList
      throw (IO.userError s!"expected no TH{code}, got: {formatted}")

-- Module-level mutation: always TH0001
def testReassignment : IO Unit := expectCode "let x = 0; x = 1;" 1
def testCompoundAssignment : IO Unit := expectCode "let x = 0; x += 1;" 1
def testIncrement : IO Unit := expectCode "let x = 0; x++;" 1
def testDecrement : IO Unit := expectCode "let x = 0; --x;" 1

-- Member/method mutation: unchanged
def testArrayIndexWrite : IO Unit := expectCode "const arr = [1]; arr[0] = 2;" 2
def testPropertyWrite : IO Unit := expectCode "const o = {x: 1}; o.x = 2;" 3
def testPushMethodCall : IO Unit := expectCode "const arr = [1]; arr.push(2);" 4
def testSortMethodCall : IO Unit := expectCode "const arr = [1]; arr.sort();" 4

-- Captured mutation: strictly TH0005 now
def testCapturedWrite : IO Unit := expectCode
  "let counter = 0; const bump = () => { counter = counter + 1; };" 5
def testCapturedReadBlocksFn : IO Unit := expectCode
  "function f(): number { let n = 0; const g = () => n; n = 1; return g(); }" 5

-- Expression-position assignment/update: TH0006
def testExprPositionAssign : IO Unit := expectCode
  "function f(): number { let n = 0; const y = (n = 1); return y; }" 6
def testExprPositionUpdate : IO Unit := expectCode
  "function f(): number { let n = 0; return n++; }" 6

-- Mutation under try/catch or @throws: TH0007
def testMutationInTry : IO Unit := expectCode
  "function f(x: number): number { let n = 0; try { n = 1; } catch (e) { return 0; } return n; }" 7
def testMutationInThrowsFn : IO Unit := expectCode
  "/** @throws RangeError */\nfunction f(x: number): number { let n = 0; n = x; if (x === 0) { throw new RangeError(\"z\"); } return n; }" 7

-- Eligible function-local mutation: still TH0001 until do-mode emission
-- lands (flipped to expectNoCode in the do-mode task).
def testEligibleStillTH1ForNow : IO Unit := expectCode
  "function f(): number { let n = 0; n = 1; return n; }" 1

-- Still-rejected forms keep TH0001
def testUninitializedLet : IO Unit := expectCode
  "function f(): number { let n: number; n = 1; return n; }" 1
def testLogicalAssignStaysTH1 : IO Unit := expectCode
  "function f(x: boolean): boolean { let b = x; b &&= x; return b; }" 1

#eval testReassignment
#eval testCompoundAssignment
#eval testIncrement
#eval testDecrement
#eval testArrayIndexWrite
#eval testPropertyWrite
#eval testPushMethodCall
#eval testSortMethodCall
#eval testCapturedWrite
#eval testCapturedReadBlocksFn
#eval testExprPositionAssign
#eval testExprPositionUpdate
#eval testMutationInTry
#eval testMutationInThrowsFn
#eval testEligibleStillTH1ForNow
#eval testUninitializedLet
#eval testLogicalAssignStaysTH1
