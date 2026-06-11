/-
  Test/Emit/LoopSubsetCheckTest.lean
  Verifies shape-aware TH0010 routing in SubsetCheck (#25):
  - Admitted for-of and canonical-for shapes in do-mode-lowerable functions
    are accepted (no TH0010).
  - Non-lowerable loops (while, for-in, destructuring heads, call RHS,
    etc.) always draw TH0010.
  - do-mode poison (try/catch, @throws, mixed admitted+while) forces TH0010
    even for otherwise-admitted shapes.
  - Module-level loops draw TH0010 (no function context).
  - Unlabeled break/continue inside admitted for-of is fine (no TH0010).
-/
import Thales.Emit.SubsetCheck
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser
open Thales.TypeCheck

private def padCode4 (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (4 - s.length) ++ s

/-- Parse src, run subsetCheckIgnoringDirectives, collect all TH#### codes
    (zero-padded to 4 digits, e.g. "TH0010"), sort them, compare to expected. -/
def expectTH (src : String) (expected : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog =>
    let diags := subsetCheckIgnoringDirectives prog
    let thCodes : List String :=
      (diags.filterMap (fun d =>
        match d.thalesCode? with
        | some n => some (s!"TH{padCode4 n}")
        | none => none)).toList.mergeSort
    let sortedExpected := expected.mergeSort
    unless thCodes == sortedExpected do
      throw (IO.userError
        s!"expected {sortedExpected}, got {thCodes}\nsrc: {src}")

-- ── Case 1: admitted for-of inside a function — no TH0010 ──
def testForOfAdmitted : IO Unit := expectTH
  "function f(xs: number[]): number { let t = 0; for (const x of xs) { t += x; } return t; }"
  []

-- ── Case 2: admitted canonical for with literal bound — no TH0010 ──
def testCanonicalForAdmitted : IO Unit := expectTH
  "function f(): number { let t = 0; for (let i = 0; i < 5; i++) { t += i; } return t; }"
  []

-- ── Case 3: while inside a function — TH0010 ──
def testWhileTH0010 : IO Unit := expectTH
  "function f(n: number): number { let i = 0; while (i < n) { i++; } return i; }"
  ["TH0010"]

-- ── Case 4: for-of with destructuring head — not admitted, TH0010 ──
-- Pattern binder (not a simple identifier) → classifyLoop = .notLowerable
def testForOfDestructuringTH0010 : IO Unit := expectTH
  "function f(xs: [number, number][]): number { let t = 0; for (const [a, b] of xs) { t += a; } return t; }"
  ["TH0010"]

-- ── Case 5: for-of with call RHS — not admitted, TH0010 ──
-- Call expression RHS → classifyLoop = .notLowerable
-- We declare g to avoid extra TS diagnostics; any extra TH codes here
-- would also come through (there are none expected beyond TH0010).
def testForOfCallRhsTH0010 : IO Unit := expectTH
  "function g(): number[] { return []; } function f(): number { let t = 0; for (const x of g()) { t += x; } return t; }"
  ["TH0010"]

-- ── Case 6: admitted for-of in a function that also contains try/catch ──
-- hasTryShape=true → doModeLowerable=false → loop gets TH0010.
-- We keep mutation out (t += x would add TH0001 too) and keep the
-- try/catch argument-free so no other THs fire.
-- try { return 0; } catch (e) { return 0; } fires hasTryShape.
-- The loop comes BEFORE the try in statement order; EscapeAnalysis still
-- poisons the whole function.
def testForOfWithTryTH0010 : IO Unit := expectTH
  "function f(xs: number[]): number { for (const x of xs) { } try { return 0; } catch (e) { return 0; } }"
  ["TH0010"]

-- ── Case 7: admitted for-of inside a @throws-annotated function → TH0010 ──
-- noMutZone=true when throwsAnn != .absent → loop admission blocked.
def testForOfThrowsFnTH0010 : IO Unit := expectTH
  "/** @throws RangeError */\nfunction f(xs: number[]): number { for (const x of xs) { } return 0; }"
  ["TH0010"]

-- ── Case 8: function with BOTH admitted for-of AND while → both TH0010 ──
-- hasUnloweredLoopShape=true (from while) → doModeLowerable=false →
-- neither loop is admitted; both draw TH0010.
-- No mutation in bodies to keep the diagnostic set clean.
def testBothAdmittedAndWhileTH0010 : IO Unit := expectTH
  "function f(xs: number[]): number { for (const x of xs) { } while (false) { } return 0; }"
  ["TH0010", "TH0010"]

-- ── Case 9: module-level (top-level) for-of → TH0010 (no function context) ──
def testTopLevelForOfTH0010 : IO Unit := expectTH
  "const xs = [1, 2, 3]; for (const x of xs) { }"
  ["TH0010"]

-- ── Case 10: unlabeled break inside admitted for-of → no TH0010 ──
-- hasLabeledBreakOrContinue checks LABELED only; unlabeled break is fine.
def testUnlabeledBreakInForOfOk : IO Unit := expectTH
  "function f(xs: number[]): number { let t = 0; for (const x of xs) { if (x < 0) { break; } t += x; } return t; }"
  []

#eval testForOfAdmitted
#eval testCanonicalForAdmitted
#eval testWhileTH0010
#eval testForOfDestructuringTH0010
#eval testForOfCallRhsTH0010
#eval testForOfWithTryTH0010
#eval testForOfThrowsFnTH0010
#eval testBothAdmittedAndWhileTH0010
#eval testTopLevelForOfTH0010
#eval testUnlabeledBreakInForOfOk
