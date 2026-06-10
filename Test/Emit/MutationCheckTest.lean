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

-- Eligible function-local mutation: in subset since do-mode emission
def testEligiblePlainAssignAllowed : IO Unit := expectNoCode
  "function f(): number { let n = 0; n = 1; return n; }" 1
def testEligibleCompoundAllowed : IO Unit := expectNoCode
  "function f(): number { let n = 0; n += 1; return n; }" 1
def testEligibleUpdateAllowed : IO Unit := expectNoCode
  "function f(): number { let n = 0; n++; return n; }" 1
-- `%=` and the bitwise compounds lower through the JS-semantics helpers
def testModAssignAllowed : IO Unit := expectNoCode
  "function f(): number { let n = 7; n %= 3; return n; }" 1
def testBitAndAssignAllowed : IO Unit := expectNoCode
  "function f(): number { let n = 7; n &= 3; return n; }" 1
-- Arrow bodies don't lower through emitFuncDecl: their own-local mutation
-- stays TH0001 in v1 even though the eligibility analysis would allow it
def testArrowOwnLocalStillTH1 : IO Unit := expectCode
  "const g = (): number => { let n = 0; n = 1; return n; };" 1

-- A switch with a `break`-style (non-returning) arm or a `default` keeps
-- the function's mutation rejected: do-mode lowers all-arms-return only
def testSwitchBreakArmStillTH1 : IO Unit := expectCode
  "function f(x: string): number { let n = 0; switch (x) { case \"a\": n = 1; break; case \"b\": return 2; } return n; }" 1

-- Still-rejected forms keep TH0001
def testUninitializedLet : IO Unit := expectCode
  "function f(): number { let n: number; n = 1; return n; }" 1
def testLogicalAssignStaysTH1 : IO Unit := expectCode
  "function f(x: boolean): boolean { let b = x; b &&= x; return b; }" 1

-- Function-level lowerability (#40/#41): mutation OUTSIDE a try, in a
-- function whose body contains one, is TH0001 (do-mode can't thread the
-- exception path; TH0007 covers only mutation inside the try)
def testMutationBesideTryTH1 : IO Unit := expectCode
  "function f(x: number): number { let n = 0; n = 5; try { return x; } catch (e) { return n; } }" 1
-- Mutation in a function that reads a null-tested variable outside its
-- test: TH0001 (#40 — do-mode's plain `if` carries no narrowing evidence)
def testNarrowedReadMutationTH1 : IO Unit := expectCode
  "function f(x: string | null): number { let n = 0; n += 1; if (x === null) { return n; } return x.length; }" 1
-- Mutating an undefined-tested variable: TH0001 (#42 — undefined tests
-- count the same as null tests)
def testUndefinedTestedMutationTH1 : IO Unit := expectCode
  "function f(x: string | undefined): number { if (x === undefined) { x = \"d\"; } return x.length; }" 1
-- A plain-identifier switch scrutinee has no do-mode lowering, even with
-- all-return arms: the function's mutation stays TH0001
def testPlainIdentSwitchTH1 : IO Unit := expectCode
  "function f(x: string): number { let n = 0; n = 1; switch (x) { case \"a\": return 1; case \"b\": return 2; } return n; }" 1

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
#eval testEligiblePlainAssignAllowed
#eval testEligibleCompoundAllowed
#eval testEligibleUpdateAllowed
#eval testModAssignAllowed
#eval testBitAndAssignAllowed
#eval testArrowOwnLocalStillTH1
#eval testSwitchBreakArmStillTH1
#eval testUninitializedLet
#eval testLogicalAssignStaysTH1
#eval testMutationBesideTryTH1
#eval testNarrowedReadMutationTH1
#eval testUndefinedTestedMutationTH1
#eval testPlainIdentSwitchTH1
