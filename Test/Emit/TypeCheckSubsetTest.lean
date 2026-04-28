/-
  Test/Emit/TypeCheckSubsetTest.lean
  Verifies TH0020-TH0025 for forbidden type forms.
-/
import Thales.Emit.SubsetCheck
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser
open Thales.TypeCheck

def expectCode' (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    unless diags.any (·.thalesCode? = some code) do
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"expected TH{code}, got: {fmt}")

def expectNoCode' (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    if diags.any (·.thalesCode? = some code) then
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"did not expect TH{code}, got: {fmt}")

/- TH0020 any -/
def testAnyParam : IO Unit := expectCode' "function f(x: any): any { return x; }" 20
def testAnyAlias : IO Unit := expectCode' "type T = any;" 20

/- TH0021 unknown -/
def testUnknownAlias : IO Unit := expectCode' "type T = unknown;" 21

/- TH0022 undiscriminated union -/
def testUndiscriminatedUnion : IO Unit :=
  expectCode' "type U = string | number;" 22

/- Discriminated union accepted (no TH0022) -/
def testDiscriminatedUnionOk : IO Unit :=
  expectNoCode'
    "type S = {kind: 'a', v: number} | {kind: 'b', v: string};"
    22

/- TH0023 intersection -/
def testIntersection : IO Unit :=
  expectCode' "type I = {a: number} & {b: string};" 23

/- TH0024 conditional / mapped -/
-- Note: if the parser doesn't support conditional types, this will fail at parse time
-- In that case it is a known gap; see comment below.
def testConditional : IO Unit :=
  expectCode' "type T<X> = X extends string ? number : boolean;" 24
def testMapped : IO Unit :=
  expectCode' "type M<T> = { [K in keyof T]: string };" 24

/- TH0025 standalone null/undefined types (rejected); nullable unions now accepted -/
def testNullInUnion : IO Unit :=
  expectNoCode' "type N = string | null;" 25
def testUndefinedInUnion : IO Unit :=
  expectNoCode' "type N = string | undefined;" 25
def testNullAlias : IO Unit :=
  expectCode' "type N = null;" 25

/- Literal unions are accepted (no TH0022): same-primitive numeric, string,
   boolean, and recursive object-literal cases. -/
def testNumericLiteralUnionOk : IO Unit :=
  expectNoCode' "type N = 1 | 2 | 3;" 22
def testSignedNumericLiteralUnionOk : IO Unit :=
  expectNoCode' "type S = -1 | 0 | 1;" 22
def testStringLiteralUnionOk : IO Unit :=
  expectNoCode' "type M = \"a\" | \"b\" | \"c\";" 22
def testBooleanLiteralUnionOk : IO Unit :=
  expectNoCode' "type B = true | false;" 22
def testLiteralObjectUnionOk : IO Unit :=
  expectNoCode' "type O = { x: 1, y: \"a\" } | { x: 2, y: \"b\" };" 22
def testRecursiveLiteralObjectUnionOk : IO Unit :=
  expectNoCode' "type O = { a: { x: 1 } } | { a: { x: 2 } };" 22

/- A union that mixes literals with non-literals is still rejected. -/
def testMixedLiteralAndPrimitiveStillRejected : IO Unit :=
  expectCode' "type U = 1 | string;" 22

#eval testAnyParam
#eval testAnyAlias
#eval testUnknownAlias
#eval testUndiscriminatedUnion
#eval testDiscriminatedUnionOk
#eval testIntersection
-- If parser rejects conditional types, testConditional will fail at parse; leave as TODO
#eval testConditional
#eval testMapped
#eval testNullInUnion
#eval testUndefinedInUnion
#eval testNullAlias
#eval testNumericLiteralUnionOk
#eval testSignedNumericLiteralUnionOk
#eval testStringLiteralUnionOk
#eval testBooleanLiteralUnionOk
#eval testLiteralObjectUnionOk
#eval testRecursiveLiteralObjectUnionOk
#eval testMixedLiteralAndPrimitiveStillRejected
