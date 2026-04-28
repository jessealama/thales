/-
  Test/Emit/LeanEmitSwitchTest.lean
  Verifies that switch statements on discriminated unions are emitted as
  Lean `match` expressions. When all constructors are covered, the
  defensive `| _ => unreachable!` tail is suppressed; a separate test
  asserts the tail is emitted for partially covered switches.
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

private def containsSubstr (h n : String) : Bool := (h.splitOn n).length ≥ 2

def expectEmit (src m : String) (needles : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog m
    for n in needles do
      unless containsSubstr out n do
        throw (IO.userError s!"missing '{n}' in:\n{out}")

def testSwitchToMatch : IO Unit := do
  let src := "
type Shape = {kind: 'circle', r: number} | {kind: 'square', s: number};
function area(shape: Shape): number {
  switch (shape.kind) {
    case 'circle': return 3.14 * shape.r * shape.r;
    case 'square': return shape.s * shape.s;
  }
}"
  expectEmit src "M"
    ["match shape with", "| .circle r =>", "| .square s =>"]

def testNoUnreachableTailWhenExhaustive : IO Unit := do
  -- Both constructors covered -> no `| _ => unreachable!` tail.
  let src := "
type T = {kind: 'a', x: number} | {kind: 'b', y: number};
function f(t: T): number {
  switch (t.kind) { case 'a': return t.x; case 'b': return t.y; }
}"
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog "M"
    if (out.splitOn "unreachable!").length ≥ 2 then
      throw (IO.userError s!"unexpected '| _ => unreachable!' tail in:\n{out}")

#eval testSwitchToMatch
#eval testNoUnreachableTailWhenExhaustive
