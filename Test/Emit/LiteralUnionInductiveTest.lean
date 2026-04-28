/-
  Test/Emit/LiteralUnionInductiveTest.lean
  Pins the inductive emission for named literal-union aliases plus the
  target-type-driven literal-position emit.
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

private def containsSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length ≥ 2

private def expectEmit (src : String) (needles : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog "M"
    for n in needles do
      unless containsSubstr out n do
        throw (IO.userError s!"missing '{n}' in:\n{out}")

/-- Numeric literal union emits an inductive with «n» constructors and a
    Coe Foo Float instance. -/
def testNumericInductive : IO Unit :=
  expectEmit
    "type Signed = -1 | 0 | 1;"
    ["inductive Signed", "«-1»", "«0»", "«1»",
     "Coe Signed Float"]

/-- String literal union emits with «"s"» constructors and Coe to String. -/
def testStringInductive : IO Unit :=
  expectEmit
    "type Mode = \"a\" | \"b\" | \"c\";"
    ["inductive Mode", "«\"a\"»", "«\"b\"»", "«\"c\"»",
     "Coe Mode String"]

/-- Boolean literal union emits as inductive with «true»/«false» and Coe
    to Bool. -/
def testBoolInductive : IO Unit :=
  expectEmit
    "type Flag = true | false;"
    ["inductive Flag", "«true»", "«false»",
     "Coe Flag Bool"]

/-- Return-position numeric literal maps to the matching constructor. -/
def testReturnNumeric : IO Unit :=
  expectEmit
    "type Signed = -1 | 0 | 1;\nfunction f(): Signed { return 0; }"
    [".«0»"]

/-- Signed numeric literal in return position maps correctly. -/
def testReturnNegative : IO Unit :=
  expectEmit
    "type Signed = -1 | 0 | 1;\nfunction f(): Signed { return -1; }"
    [".«-1»"]

/-- String literal in return position maps to the matching constructor. -/
def testReturnString : IO Unit :=
  expectEmit
    "type Mode = \"a\" | \"b\";\nfunction f(): Mode { return \"a\"; }"
    [".«\"a\"»"]

/-- Boolean literal in return position maps to the matching constructor. -/
def testReturnBoolean : IO Unit :=
  expectEmit
    "type Flag = true | false;\nfunction f(): Flag { return true; }"
    [".«true»"]

/-- Annotated const initializer maps to the matching constructor. -/
def testInitNumeric : IO Unit :=
  expectEmit
    "type Signed = -1 | 0 | 1;\nconst x: Signed = 0;"
    [".«0»"]

/-- Annotated const initializer maps for string literal-union too. -/
def testInitString : IO Unit :=
  expectEmit
    "type Mode = \"a\" | \"b\";\nconst m: Mode = \"a\";"
    [".«\"a\"»"]

#eval testNumericInductive
#eval testStringInductive
#eval testBoolInductive
#eval testReturnNumeric
#eval testReturnNegative
#eval testReturnString
#eval testReturnBoolean
#eval testInitNumeric
#eval testInitString
