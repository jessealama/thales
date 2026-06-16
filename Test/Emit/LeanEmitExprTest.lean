/-
  Test/Emit/LeanEmitExprTest.lean
  Exercises `emitExpr` via minimal single-return function declarations.
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

private def containsSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length ≥ 2

def expectEmit (src moduleName : String) (needles : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog moduleName
    for n in needles do
      unless containsSubstr out n do
        throw (IO.userError s!"missing '{n}' in:\n{out}")

/-- Like `expectEmit`, but additionally asserts that none of `forbidden`
    appears in the emitted Lean. Useful for confirming that TS-only
    constructs (like `as const`, `satisfies`) are erased. -/
def expectEmitWithout
    (src moduleName : String) (needles forbidden : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog moduleName
    for n in needles do
      unless containsSubstr out n do
        throw (IO.userError s!"missing '{n}' in:\n{out}")
    for f in forbidden do
      if containsSubstr out f then
        throw (IO.userError s!"unexpected '{f}' in:\n{out}")

def testSimpleReturn : IO Unit :=
  expectEmit "function id(x: number): number { return x; }" "M"
    ["def id", "(x : Float)", ": Float", "x"]

def testArithmetic : IO Unit :=
  expectEmit "function add(x: number, y: number): number { return x + y; }" "M"
    ["def add", "(x + y)"]

def testTernary : IO Unit :=
  expectEmit "function max(x: number, y: number): number { return x > y ? x : y; }" "M"
    ["if (x > y) then x else y"]

def testEquality : IO Unit :=
  expectEmit "function eq(x: number, y: number): boolean { return x === y; }" "M"
    ["(x == y)"]

def testBigintLit : IO Unit :=
  expectEmit "function ten(): bigint { return 10n; }" "M"
    ["def ten", ": Int"]

def testStringLit : IO Unit :=
  expectEmit "function greet(): string { return \"hello\"; }" "M"
    ["def greet", ": String", "\"hello\""]

def testBoolLit : IO Unit :=
  expectEmit "function yes(): boolean { return true; }" "M"
    ["def yes", ": Bool", "true"]

def testLogicalAnd : IO Unit :=
  expectEmit "function both(a: boolean, b: boolean): boolean { return a && b; }" "M"
    ["(a && b)"]

def testLogicalOr : IO Unit :=
  expectEmit "function either(a: boolean, b: boolean): boolean { return a || b; }" "M"
    ["(a || b)"]

def testCall : IO Unit :=
  expectEmit "function callF(f: (x: number) => number, x: number): number { return f(x); }" "M"
    ["(f x)"]

def testArrowBody : IO Unit :=
  expectEmit "function applyTwice(f: (x: number) => number, x: number): number { return f(f(x)); }" "M"
    ["def applyTwice"]

/-- `x as const` is a TS-only annotation that constrains inference. It must
    parse and then erase to the underlying expression on emit. -/
def testAsConstString : IO Unit :=
  expectEmitWithout "function tag(): string { return \"hi\" as const; }" "M"
    ["def tag", "\"hi\""] ["as const", "as_"]

/-- Chained `as` casts (`x as unknown as string`) must also parse and erase. -/
def testAsChained : IO Unit :=
  expectEmitWithout
    "function pun(x: number): string { return x as unknown as string; }" "M"
    ["def pun"] ["as ", "unknown"]

#eval testSimpleReturn
#eval testArithmetic
#eval testTernary
#eval testEquality
#eval testBigintLit
#eval testStringLit
#eval testBoolLit
#eval testLogicalAnd
#eval testLogicalOr
#eval testCall
#eval testArrowBody
#eval testAsConstString
#eval testAsChained

-- xs[i] lowers to the JS-semantics indexRead (Float index, Option result),
-- not the Nat-indexed Array.get?.
def testIndexReadLowering : IO Unit :=
  expectEmitWithout
    "const words: string[] = [\"a\", \"b\"];
function at1(i: number): string | undefined { return words[i]; }" "M"
    ["Thales.TS.indexRead", "words", "i"]
    ["Thales.TS.Array.get?"]

-- A null test on a binding the emitter has no recorded type for (here: an
-- element read off an inline callback's contextually-typed parameter) must
-- still lower to the narrowing match: a plain `ite` would return the
-- operand at `Option` type and fail elaboration.
def testUnknownBindingNarrowingMatch : IO Unit :=
  expectEmitWithout
    "function apply(callback: (xs: number[]) => number): number { return callback([1, 2]); }
const result = apply((xs) => {
  const hit = xs[0];
  if (hit !== undefined) {
    return hit;
  }
  return 42;
});" "M"
    ["match hit with", ".some hit"]
    ["if hit.isSome"]

-- A definedness test on a recorded NON-Option binding (param `x : String`)
-- is vacuous: it folds to `if true`/`if false`, never `x.isSome` (which
-- does not exist on `String`).
def testDefinednessFoldsOnNonOptionParam : IO Unit :=
  expectEmitWithout
    "function f(x: string): string { if (x !== undefined) { return x; } return \"none\"; }" "M"
    ["def f", "if true then"]
    ["isSome", "isNone"]

#eval testIndexReadLowering
#eval testUnknownBindingNarrowingMatch
#eval testDefinednessFoldsOnNonOptionParam
