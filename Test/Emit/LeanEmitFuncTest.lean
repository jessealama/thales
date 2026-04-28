/-
  Test/Emit/LeanEmitFuncTest.lean
  Exercises `emitFuncDecl` and `emitBody` for multi-statement function bodies
  and arrow functions assigned to `const`.
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

private def containsSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length ≥ 2

def expectEmitFunc (src moduleName : String) (needles : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog moduleName
    for n in needles do
      unless containsSubstr out n do
        throw (IO.userError s!"missing '{n}' in:\n{out}")

-- `const y = x * x; return y;` should produce a let binding
def testLetChain : IO Unit :=
  expectEmitFunc
    "function sq(x: number): number { const y = x * x; return y; }" "M"
    ["def sq", "(x : Float)", ": Float", "let y", "x * x"]

-- Recursive factorial with if/else
def testRecursiveFact : IO Unit :=
  expectEmitFunc
    "function fact(n: bigint): bigint { if (n === 0n) { return 1n; } else { return n * fact(n - 1n); } }" "M"
    ["def fact", "(n : Int)", ": Int", "if", "then", "else"]

-- Arrow function assigned to const — type info not available from arrow AST,
-- so param/return types default to Unit; verify the def and body are emitted.
def testArrowFunction : IO Unit :=
  expectEmitFunc
    "const double = (x: number): number => x * 2;" "M"
    ["def double", "x * 2"]

-- Multi-statement body with multiple let bindings
def testMultiLet : IO Unit :=
  expectEmitFunc
    "function sum3(a: number, b: number, c: number): number { const ab = a + b; const abc = ab + c; return abc; }" "M"
    ["def sum3", "let ab", "let abc", "a + b", "ab + c"]

-- If statement with both branches returning values
def testIfElseReturn : IO Unit :=
  expectEmitFunc
    "function abs(x: number): number { if (x < 0) { return -x; } else { return x; } }" "M"
    ["def abs", "if", "then", "else"]

#eval testLetChain
#eval testRecursiveFact
#eval testArrowFunction
#eval testMultiLet
#eval testIfElseReturn
