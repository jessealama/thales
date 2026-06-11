/-
  Test/Emit/LoopEmitTest.lean
  Pins #25 do-mode loop lowering: for-of and canonical-for loops inside
  Id.run do bodies. Break/continue, element-type threading, Nat/Float shim,
  and @total entry. Failing tests first (TDD).
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

private def containsSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length ≥ 2

/-- Check that the emitted output of `src` contains every needle and none of
    the forbidden strings. -/
def expectEmitLoop (src : String) (needles : List String)
    (forbidden : List String := []) : IO Unit := do
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

-- 1. For-of accumulation: sum xs. The compound-assign `total += x` in
-- do-mode emits `total := (total + x)` via the existing compound-assign arm.
def testForOfAccumulation : IO Unit :=
  expectEmitLoop
    "function sum(xs: number[]): number { let total = 0; for (const x of xs) { total += x; } return total; }"
    ["Id.run do", "let mut total", "for x in xs do", "total := (total + x)", "return total"]

-- 2. Loop-without-mutation triggers do-mode entry (hasLowerableLoop flag).
-- `contains` has no mutation, only a for-of with an early return inside.
def testLoopTriggersDoMode : IO Unit :=
  expectEmitLoop
    "function has(xs: number[], y: number): boolean { for (const x of xs) { if (x === y) { return true; } } return false; }"
    ["Id.run do", "for x in xs do", "return true", "return false"]

-- 3. Break/continue lower to `break` / `continue` in the do-block.
def testBreakContinue : IO Unit :=
  expectEmitLoop
    "function f(xs: number[]): number { let t = 0; for (const x of xs) { if (x < 0) { break; } if (x === 0) { continue; } t += x; } return t; }"
    ["for x in xs do", "break", "continue"]

-- 4. Canonical for with literal bound: `for (let i = 0; i < 5; i++)` →
-- range loop + Float shim for `i` in the body.
def testCanonicalLiteralBound : IO Unit :=
  expectEmitLoop
    "function f(): number { let t = 0; for (let i = 0; i < 5; i++) { t += i; } return t; }"
    ["for i in [0:5] do", "let i : Float := i.toFloat"]

-- 5. Canonical for bounded by `arr.length`: `i < xs.length` → `[0:xs.size]`
--    (Lean `Array` has `.size`; the Float-valued `arr.length` lowering is for
--    expression positions, not range bounds).
def testCanonicalLengthBound : IO Unit :=
  expectEmitLoop
    "function f(xs: number[]): number { let t = 0; for (let i = 0; i < xs.length; i++) { t += i; } return t; }"
    ["for i in [0:xs.size] do"]

-- 6. Nested for-of: outer and inner `for … in … do` both present.
def testNestedForOf : IO Unit :=
  expectEmitLoop
    "function cross(xs: number[], ys: number[]): number { let t = 0; for (const x of xs) { for (const y of ys) { t += x * y; } } return t; }"
    ["for x in xs do", "for y in ys do"]

-- 7. Element-type threading: for-of over a `string[]` param where the body
-- does string concatenation. `out + x` on strings lowers to Lean's `+`
-- operator (the runtime provides an Add String instance via String.append).
-- The emitted form is `(out + x)` — no `++`, just `+` via binaryOpStr .add.
def testStringElementType : IO Unit :=
  expectEmitLoop
    "function join(xs: string[]): string { let out = \"\"; for (const x of xs) { out = out + x; } return out; }"
    ["for x in xs do", "out := (out + x)"]

-- 8. @total for-of emits `def` not `partial def`. A for-of body is
-- structurally total (Array.ForIn terminates). The @total directive
-- triggers lake-backed termination verification, but we only check emission
-- here (not the full lake verify).
def testTotalForOf : IO Unit :=
  expectEmitLoop
    "/** @total */\nfunction product(xs: number[]): number { let p = 1; for (const x of xs) { p *= x; } return p; }"
    ["def product"]
    (forbidden := ["partial def product"])

-- 9. Defence-in-depth: a canonical-for bounded by a non-array `.length`
-- (here a string parameter) must render the loud marker, never `[0:s.size]`
-- (String has no `.size`; length semantics diverge). SubsetCheck rejects
-- this upstream; the emitter guard covers phase drift.
def testStringLengthBoundLoudMarker : IO Unit :=
  expectEmitLoop
    "function f(s: string): number { let t = 0; for (let i = 0; i < s.length; i++) { t += i; } return t; }"
    ["(unsupported"]
    (forbidden := ["[0:s.size]"])

#eval testForOfAccumulation
#eval testLoopTriggersDoMode
#eval testBreakContinue
#eval testCanonicalLiteralBound
#eval testCanonicalLengthBound
#eval testNestedForOf
#eval testStringElementType
#eval testTotalForOf
#eval testStringLengthBoundLoudMarker
