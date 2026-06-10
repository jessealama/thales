/-
  Test/Emit/DoModeEmitTest.lean
  Pins #24 do-mode emission: a function body containing an eligible
  statement-position mutation lowers to `Id.run do` with `let mut`;
  functions without eligible mutation keep the pure expression path.
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

private def containsSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length ≥ 2

def expectEmit (src : String) (needles : List String) (forbidden : List String := []) : IO Unit := do
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

-- straight-line plain reassignment lowers to Id.run do / let mut
def testStraightLineDo : IO Unit :=
  expectEmit
    "function inc(): number { let n = 0; n = n + 1; return n; }
console.log(inc());"
    ["def inc : Float :=",
     "Id.run do",
     "let mut n := 0.000000",
     "n := (n + 1.000000)",
     "return n"]

-- a function without mutation keeps the pure let-chain path (no do-block)
def testPureStaysPure : IO Unit :=
  expectEmit
    "function sq(x: number): number { const y = x * x; return y; }
console.log(sq(3));"
    ["def sq"]
    (forbidden := ["Id.run do", "let mut"])

-- non-mutated lets inside a do-mode body stay immutable `let`
def testMixedLets : IO Unit :=
  expectEmit
    "function f(): number { const k = 10; let n = 0; n = n + k; return n; }
console.log(f());"
    ["Id.run do", "let k := 10.000000", "let mut n := 0.000000", "n := (n + k)"]
    (forbidden := ["let mut k"])

#eval testStraightLineDo
#eval testPureStaysPure
#eval testMixedLets
