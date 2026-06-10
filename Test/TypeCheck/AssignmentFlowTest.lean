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

#eval t0
#eval t1
#eval t2
#eval t3
#eval t4
#eval t5
#eval t6
