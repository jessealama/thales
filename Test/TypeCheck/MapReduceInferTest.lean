/-
  Test/TypeCheck/MapReduceInferTest.lean
  Pins return-type inference for `Array.map` / `Array.reduce` with inline
  monomorphic callbacks. Before 0.7, `map` returned `Array<any>` and
  `reduce` returned `any`, so a wrongly-typed target silently type-checked.
-/
import Thales.TypeCheck.Check
import Thales.Parser.Native

open Thales.TypeCheck
open Thales.Parser

private def tsCodes (diags : Array Diagnostic) : List Nat :=
  diags.toList.filterMap fun d =>
    match d.kind with
    | .thales _ => none
    | k => some k.tscCode

def expectTSCodes (src : String) (expected : List Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := typeCheck prog
    let got := tsCodes diags
    unless got == expected do
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"\nexpected codes {expected}\ngot codes     {got}\nfull diags: {fmt}")

def testMapWrongTarget : IO Unit :=
  expectTSCodes
    ("const xs = [1, 2, 3];\n" ++
     "const ys: string[] = xs.map((x) => x * 2);\n")
    [2322]

def testMapRightTarget : IO Unit :=
  expectTSCodes
    ("const xs = [1, 2, 3];\n" ++
     "const ys: number[] = xs.map((x) => x * 2);\n")
    []

def testReduceWrongTarget : IO Unit :=
  expectTSCodes
    ("const xs = [1, 2, 3];\n" ++
     "const s: string = xs.reduce((a, b) => a + b, 0);\n")
    [2322]

def testReduceRightTarget : IO Unit :=
  expectTSCodes
    ("const xs = [1, 2, 3];\n" ++
     "const total: number = xs.reduce((a, b) => a + b, 0);\n")
    []

#eval! testMapWrongTarget
#eval! testMapRightTarget
#eval! testReduceWrongTarget
#eval! testReduceRightTarget
