/-
  Test/Runtime/IndexReadTest.lean
  Pins `indexRead`, the JS-semantics array element read (`xs[i]` with a
  `number` index). Every expected value is Node's result for
  `["a","b","c"][i]`: fractional, negative, NaN, infinite, non-safe-integer,
  and out-of-bounds indices read as `undefined`; `-0` reads element 0.
-/
import Thales.TS.Runtime

open Thales.TS

private def expectOpt (label : String) (got expected : Option String) : IO Unit := do
  unless got == expected do
    throw (IO.userError s!"{label}: got {repr got}, expected {repr expected}")

private def xs : Array String := #["a", "b", "c"]

def tInBounds : IO Unit := do
  expectOpt "xs[0]" (indexRead xs 0.0) (some "a")
  expectOpt "xs[2]" (indexRead xs 2.0) (some "c")
  expectOpt "xs[-0]" (indexRead xs (-0.0)) (some "a")

def tUndefined : IO Unit := do
  expectOpt "xs[3]" (indexRead xs 3.0) none
  expectOpt "xs[-1]" (indexRead xs (-1.0)) none
  expectOpt "xs[1.5]" (indexRead xs 1.5) none
  expectOpt "xs[NaN]" (indexRead xs (0.0 / 0.0)) none
  expectOpt "xs[Infinity]" (indexRead xs (1.0 / 0.0)) none
  expectOpt "xs[2^53]" (indexRead xs 9007199254740992.0) none

#eval tInBounds
#eval tUndefined
