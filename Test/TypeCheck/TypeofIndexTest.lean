/-
  Test/TypeCheck/TypeofIndexTest.lean
  Pins type-resolution for `(typeof X)[number]` — the TS idiom for
  deriving the element type of an array-typed value.
-/
import Thales.TypeCheck.Check
import Thales.Parser.Native

open Thales.TypeCheck
open Thales.Parser

/-- Extract just the TS-category diagnostic codes from a typeCheck result. -/
private def tsCodes (diags : Array Diagnostic) : List Nat :=
  diags.toList.filterMap fun d =>
    match d.kind with
    | .thales _ => none
    | k => some k.tscCode

/-- Type-check `src` and assert the resulting TS-category diagnostic codes
    match `expected`. Thales-category (TH####) diagnostics are ignored. -/
def expectTSCodes (src : String) (expected : List Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := typeCheck prog
    let got := tsCodes diags
    unless got == expected do
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"\nexpected codes {expected}\ngot codes     {got}\nfull diags: {fmt}")

/-- `(typeof MODES)[number]` resolves to the element type of MODES.
    String literal flows OK; numeric literal does not. -/
def testTypeofIndexElement : IO Unit :=
  expectTSCodes
    ("const MODES: string[] = [\"a\", \"b\", \"c\"];\n" ++
     "type Mode = (typeof MODES)[number];\n" ++
     "function pick(): Mode { return \"a\"; }\n")
    []

def testTypeofIndexElementWrongType : IO Unit :=
  expectTSCodes
    ("const MODES: string[] = [\"a\", \"b\", \"c\"];\n" ++
     "type Mode = (typeof MODES)[number];\n" ++
     "function pick(): Mode { return 42; }\n")
    [2322]

/-- For a non-array operand, `(typeof X)[number]` resolves to `.any` —
    we don't reject usages we cannot model. -/
def testTypeofIndexNonArrayFallback : IO Unit :=
  expectTSCodes
    ("const x: number = 5;\n" ++
     "type T = (typeof x)[number];\n" ++
     "function f(): T { return \"anything\"; }\n")
    []

#eval! testTypeofIndexElement
#eval! testTypeofIndexElementWrongType
#eval! testTypeofIndexNonArrayFallback
