/-
  Test/TypeCheck/AssignmentFlowTest.lean
  Pins #24's tsc-style assignment typing and flow updates. Every
  expectation here was cross-checked against tsc 6.0 (--strict):
    * assignment RHS checks against the DECLARED type (annotation or
      widened initializer) → TS2322;
    * compound `x OP= y` types as `x = x OP y` (so `s += 1` on string is
      clean — string concatenation — and never a raw-RHS TS2322);
    * after `x = e`, the flow type is the widened RHS narrowed against
      the declared type (so a nullable that was just assigned a string
      is not "possibly null").
-/
import Thales.TypeCheck.Check
import Thales.Parser.Native

open Thales.TypeCheck
open Thales.Parser

private def diagsOf (src : String) : IO (Array Diagnostic) := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog => return typeCheck prog

private def hasTS (d : Diagnostic) (code : Nat) : Bool :=
  ((d.format "t.ts").splitOn s!"error TS{code}:").length > 1

def expectTS (src : String) (code : Nat) : IO Unit := do
  let diags ← diagsOf src
  unless diags.any (hasTS · code) do
    let formatted := (diags.map (·.format "t.ts")).toList
    throw (IO.userError s!"expected TS{code}, got: {formatted}")

def expectNoTS (src : String) (code : Nat) : IO Unit := do
  let diags ← diagsOf src
  if diags.any (hasTS · code) then
    let formatted := (diags.map (·.format "t.ts")).toList
    throw (IO.userError s!"expected no TS{code}, got: {formatted}")

-- pin: annotated declared type already checks assignments (pre-#24 behavior)
def t0 : IO Unit := expectTS
  "function f(): number { let n: number = 0; n = \"x\"; return n; }" 2322
-- widened-initializer declared type: `let n = 0` declares number
def t1 : IO Unit := expectTS
  "function f(): number { let n = 0; n = \"x\"; return n; }" 2322
-- compound op types as `s = s + 1` (string concat) — tsc is clean here;
-- a raw-RHS check would wrongly emit TS2322
def t2 : IO Unit := expectNoTS
  "function f(): string { let s = \"a\"; s += 1; return s; }" 2322
-- `n *= \"x\"`: tsc emits TS2363 (arithmetic operand) which thales does not
-- implement (pre-existing gap, see follow-ups); the desugar must at least
-- not mis-report it as TS2322
def t3 : IO Unit := expectNoTS
  "function f(): number { let n = 2; n *= \"x\"; return n; }" 2322
-- flow update: after `x = \"a\"`, x is string — tsc is clean; thales's
-- possibly-null surrogate TS2339 must not fire
def t4 : IO Unit := expectNoTS
  "function f(x: string | null): number { x = \"a\"; return x.length; }" 2339
-- ordinary numeric reassignment stays clean
def t5 : IO Unit := expectNoTS
  "function f(): number { let n = 0; n = n + 1; return n; }" 2322
-- the widened declared type is the BASE type, not the literal: `n = 5`
-- after `let n = 0` is fine
def t6 : IO Unit := expectNoTS
  "function f(): number { let n = 0; n = 5; return n; }" 2322

-- ── if/else joins (cross-checked against tsc --strict) ──

-- both branches assign a string: join is string — tsc clean, no
-- possibly-null surrogate TS2339
def j1 : IO Unit := expectNoTS
  "function f(c: boolean, x: string | null): number { if (c) { x = \"a\"; } else { x = \"b\"; } return x.length; }" 2339
-- early-return branch contributes nothing: continuation gets the negated
-- guard (x non-null) — tsc clean
def j2 : IO Unit := expectNoTS
  "function f(x: string | null): number { if (x === null) { return 0; } return x.length; }" 2339
-- assignment in a nested branch invalidates narrowing: after the inner
-- if, x is string|null again — tsc flags x.length (TS18047); thales's
-- surrogate is TS2339, which must now fire
def j3 : IO Unit := expectTS
  "function f(c: boolean, x: string | null): number { if (x !== null) { if (c) { x = null; } return x.length; } return 0; }" 2339
-- no-else assignment joins with the fall-through path: x stays possibly
-- null after `if (c) { x = \"a\"; }` — tsc flags x.length
def j4 : IO Unit := expectTS
  "function f(c: boolean, x: string | null): number { if (c) { x = \"a\"; } return x.length; }" 2339
-- assignment before the if, then both paths keep it: still clean
def j5 : IO Unit := expectNoTS
  "function f(c: boolean, x: string | null): number { x = \"a\"; if (c) { x = \"b\"; } return x.length; }" 2339

-- ── loop checks (cross-checked against tsc --strict) ──

-- for-init var visible inside body: `i` is in scope — no TS2304
def l1 : IO Unit := expectNoTS
  "function f(): number { let s = 0; for (let i = 0; i < 3; i++) { s += i; } return s; }" 2304
-- for-of element type enforced: `x` is number, assigned to string — TS2322
def l2 : IO Unit := expectTS
  "function f(xs: number[]): void { for (const x of xs) { const y: string = x; } }" 2322
-- for-of head visible inside body: `x` is in scope — no TS2304
def l3 : IO Unit := expectNoTS
  "function f(xs: number[]): number { let s = 0; for (const x of xs) { s += x; } return s; }" 2304

#eval t0
#eval t1
#eval t2
#eval t3
#eval t4
#eval t5
#eval t6
#eval j1
#eval j2
#eval j3
#eval j4
#eval j5
#eval l1
#eval l2
#eval l3
