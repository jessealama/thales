/-
  Test/Emit/LeanEmitUnionTest.lean
  Verifies that discriminated union type aliases are emitted as Lean
  inductive types, and that non-discriminated unions fall back to abbrev.
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

private def containsSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length ≥ 2

def expectContains (src moduleName : String) (needles : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog moduleName
    for n in needles do
      unless containsSubstr out n do
        throw (IO.userError s!"missing '{n}' in:\n{out}")

def testDiscriminatedUnion : IO Unit :=
  expectContains
    "type Shape = {kind: 'circle', r: number} | {kind: 'square', s: number};"
    "M"
    ["inductive Shape", "| circle (r : Float)", "| square (s : Float)"]

def testUnionWithBigint : IO Unit :=
  expectContains
    "type N = {kind: 'a', v: bigint} | {kind: 'b'};"
    "M"
    ["inductive N", "| a (v : Int)", "| b"]

def testNonDiscriminatedUnionFallback : IO Unit :=
  -- string | number has no shared string-lit property, so falls back to abbrev
  expectContains
    "type Prim = string | number;"
    "M"
    ["abbrev Prim"]

def testInductiveDeriving : IO Unit :=
  -- inductive must derive Repr
  expectContains
    "type Event = {kind: 'click', x: number} | {kind: 'key', code: string};"
    "M"
    ["deriving Repr"]

#eval testDiscriminatedUnion
#eval testUnionWithBigint
#eval testNonDiscriminatedUnionFallback
#eval testInductiveDeriving
