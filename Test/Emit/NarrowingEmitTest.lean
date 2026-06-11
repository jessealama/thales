/-
  Test/Emit/NarrowingEmitTest.lean
  Pins the null/undefined-test `if` lowering on the pure path (#43): a
  positive test (`x === null`) lowers to an Option match with the THEN
  branch in the none arm; a negated test (`x !== null`) swaps the arms so
  the THEN branch gets the some-rebinding. Both forms require the THEN
  branch to return on every path; otherwise the plain-ite fallback is kept.
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

private def containsSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length ≥ 2

def expectEmitN (src : String) (needles : List String) (forbidden : List String := []) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog "M"
    for n in needles do
      unless containsSubstr out n do
        throw (IO.userError s!"missing '{n}' in:\n{out}")
    for n in forbidden do
      if containsSubstr out n then
        throw (IO.userError s!"unexpected '{n}' in:\n{out}")

-- positive test: none arm is the THEN branch, continuation rebinds via some
def testPositiveNullMatch : IO Unit :=
  expectEmitN
    "function a(x: string | null): number { if (x === null) { return 0; } return x.length; }
console.log(a(\"hi\"));"
    ["match x with", "| .none =>", "| .some x =>", "x.length.toFloat"]

-- negated test (#43): arms swap — THEN gets the some-rebinding, so the
-- narrowed read compiles
def testNegatedNullMatch : IO Unit :=
  expectEmitN
    "function b(x: string | null): number { if (x !== null) { return x.length; } return 0; }
console.log(b(\"hi\"));"
    ["match x with", "| .some x =>", "x.length.toFloat", "| .none =>", "0.000000"]
    (forbidden := ["if x.isSome"])

-- negated undefined test lowers the same way
def testNegatedUndefinedMatch : IO Unit :=
  expectEmitN
    "function c(x: string | undefined): number { if (x !== undefined) { return x.length; } return 0; }
console.log(c(\"hi\"));"
    ["match x with", "| .some x =>", "x.length.toFloat"]
    (forbidden := ["if x.isSome"])

-- reversed operand order
def testNegatedReversedOperands : IO Unit :=
  expectEmitN
    "function d(x: string | null): number { if (null !== x) { return x.length; } return 0; }
console.log(d(\"hi\"));"
    ["match x with", "| .some x =>"]

-- a THEN branch that does not return keeps the ite fallback (the match
-- arms carry no continuation, so fall-through would skip it)
def testNonReturningThnFallsBack : IO Unit :=
  expectEmitN
    "function e(x: string | null): number { if (x !== null) { const y = 1; } return 0; }
console.log(e(\"hi\"));"
    ["if x.isSome"]
    (forbidden := ["match x with"])

#eval testPositiveNullMatch
#eval testNegatedNullMatch
#eval testNegatedUndefinedMatch
#eval testNegatedReversedOperands
#eval testNonReturningThnFallsBack
