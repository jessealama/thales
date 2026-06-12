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

-- `n++` / `n--` desugar to plain reassignment on the underlying binop
def testUpdateDesugar : IO Unit :=
  expectEmit
    "function f(): number { let n = 0; n++; n--; return n; }
console.log(f());"
    ["Id.run do",
     "n := (n + 1.000000)",
     "n := (n - 1.000000)"]

-- compound ops desugar to `n := n OP e`; `**=` lowers through `^`
def testCompoundDesugar : IO Unit :=
  expectEmit
    "function f(): number { let m = 10; m += 2; m -= 1; m *= 4; m /= 8; m **= 2; return m; }
console.log(f());"
    ["Id.run do",
     "m := (m + 2.000000)",
     "m := (m - 1.000000)",
     "m := (m * 4.000000)",
     "m := (m / 8.000000)",
     "m := (m ^ 2.000000)"]

-- mutated parameters self-shadow as `let mut x := x` (JS param mutation
-- never affects the caller, so a local mutable copy is exact)
def testParamSelfShadow : IO Unit :=
  expectEmit
    "function pad(n: number): number { n = n + 1; return n; }
console.log(pad(2));"
    ["def pad (n : Float) : Float :=",
     "Id.run do",
     "let mut n := n",
     "n := (n + 1.000000)",
     "return n"]

-- unmutated parameters get no shadow
def testUnmutatedParamNoShadow : IO Unit :=
  expectEmit
    "function f(x: number, y: number): number { x += y; return x; }
console.log(f(1, 2));"
    ["let mut x := x"]
    (forbidden := ["let mut y"])

-- no-else `if` with mutation: the branch lowers WITHOUT the continuation
-- appended (do-notation has statement semantics), so the post-branch
-- mutation stays visible after the `if`
def testBranchMutationDo : IO Unit :=
  expectEmit
    "function f(c: boolean): number { let n = 0; if (c) { n += 5; } n += 1; return n; }
console.log(f(true));"
    ["Id.run do", "if c then", "n := (n + 5.000000)",
     "n := (n + 1.000000)", "return n"]

-- early return inside a branch is do-notation's native `return`
def testEarlyReturnDo : IO Unit :=
  expectEmit
    "function g(n: number): number { let m = n; if (m > 10) { return 100; } m += 1; return m; }
console.log(g(20));
console.log(g(1));"
    ["let mut m := n", "if (m > 10.000000) then", "return 100.000000",
     "m := (m + 1.000000)", "return m"]

-- if/else where both branches return: no dead trailing `return ()`
def testIfElseBothReturn : IO Unit :=
  expectEmit
    "function h(c: boolean): number { let n = 1; if (c) { n += 1; return n; } else { return 0; } }
console.log(h(true));"
    ["if c then", "n := (n + 1.000000)", "return n", "else", "return 0.000000"]
    (forbidden := ["return ()"])

-- ── function-level lowerability fallback (#40/#41): even with eligible
-- mutation, an unlowerable body shape must keep the PURE emission path
-- (SubsetCheck rejects these programs; the emitter gate is the
-- defense-in-depth that turns a checker regression into a pure-path
-- emission instead of a miscompile) ──

-- try/catch in the body: no do-mode
def testTryBodyStaysPure : IO Unit :=
  expectEmit
    "function f(x: number): number { let n = 0; n = 5; try { return x; } catch (e) { return n; } }
console.log(f(3));"
    ["def f"]
    (forbidden := ["Id.run do", "let mut"])

-- null-tested `x` read outside its test no longer poisons do-mode: the
-- statement-position match rebinds `x` and, because the THEN branch
-- returns, the continuation joins the some-arm at the narrowed type
def testNarrowedReadLowersInDo : IO Unit :=
  expectEmit
    "function f(x: string | null): number { let n = 0; n += 1; if (x === null) { return n; } return x.length; }
console.log(f(\"abc\"));"
    ["def f", "Id.run do", "let mut n", "match x with", ".none", ".some x", "x.length"]

#eval testStraightLineDo
#eval testPureStaysPure
#eval testMixedLets
#eval testUpdateDesugar
#eval testCompoundDesugar
#eval testParamSelfShadow
#eval testUnmutatedParamNoShadow
#eval testBranchMutationDo
#eval testEarlyReturnDo
#eval testIfElseBothReturn
#eval testTryBodyStaysPure
#eval testNarrowedReadLowersInDo

-- A const local bound to an element read narrows via a statement-position
-- match in do-mode: the some-arm rebinds the name at the unwrapped type
-- and `return` keeps do-notation's native early exit.
def testDoModeOptionNarrow : IO Unit :=
  expectEmit
    "const cache: string[] = [\"\", \" \"];
function f(n: number): string {
  let out = \"\";
  while (out.length < n) {
    const hit = cache[n];
    if (hit !== undefined) {
      return hit;
    }
    out = out + \"x\";
  }
  return out;
}"
    ["match hit with", "some hit =>", "none =>"]
    ["hit.isSome"]

#eval testDoModeOptionNarrow
