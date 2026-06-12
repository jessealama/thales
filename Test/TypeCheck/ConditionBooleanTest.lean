/-
  Test/TypeCheck/ConditionBooleanTest.lean
  Pins TH0026: condition positions and `!`/`&&`/`||` operands must be
  boolean (see `requireBooleanCondition`). tsc accepts all of these
  programs; TH0026 is a subset boundary, not a tsc mirror.
-/
import Thales.TypeCheck.Check
import Thales.Parser.Native

open Thales.TypeCheck
open Thales.Parser

private def diagsOf (src : String) : IO (Array Diagnostic) := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog => return typeCheck prog

private def expectTH0026 (src : String) : IO Unit := do
  let diags ← diagsOf src
  unless diags.any (·.thalesCode? == some 26) do
    let formatted := (diags.map (·.format "t.ts")).toList
    throw (IO.userError s!"expected TH0026, got: {formatted}")

private def expectNoTH0026 (src : String) : IO Unit := do
  let diags ← diagsOf src
  if diags.any (·.thalesCode? == some 26) then
    let formatted := (diags.map (·.format "t.ts")).toList
    throw (IO.userError s!"expected no TH0026, got: {formatted}")

-- ── non-boolean conditions draw TH0026 ──────────────────────────────────────

def t_ifNumber : IO Unit := expectTH0026
  "function f(n: number): number { if (n) { return 1; } return 0; }"
def t_ifString : IO Unit := expectTH0026
  "function f(s: string): number { if (s) { return 1; } return 0; }"
def t_whileNumber : IO Unit := expectTH0026
  "function f(n: number): number { let k = n; while (k) { k -= 1; } return k; }"
def t_doWhileNumber : IO Unit := expectTH0026
  "function f(n: number): number { let k = n; do { k -= 1; } while (k); return k; }"
def t_forNumberTest : IO Unit := expectTH0026
  "function f(n: number): number { let t = 0; for (let i = n; i; i -= 1) { t += i; } return t; }"
def t_ternaryNumber : IO Unit := expectTH0026
  "function f(n: number): string { return n ? \"some\" : \"none\"; }"

-- `!`/`&&`/`||` synthesize boolean-ish result types, so the condition-position
-- check alone would let truthy operands through; the operand check fires.
def t_notNumber : IO Unit := expectTH0026
  "function f(n: number): number { if (!n) { return 1; } return 0; }"
def t_andNumberLeft : IO Unit := expectTH0026
  "function f(n: number, b: boolean): number { if (n && b) { return 1; } return 0; }"
def t_orNumberRight : IO Unit := expectTH0026
  "function p(n: number): boolean { return n > 0; } function g(n: number): number { if (p(n) || n) { return 1; } return 0; }"
-- the operand rule applies outside condition positions too: `||` as a
-- truthy default has no Lean-side meaning
def t_orDefaultString : IO Unit := expectTH0026
  "function pick(s: string): string { return s || \"fallback\"; }"

-- ── boolean conditions stay clean ────────────────────────────────────────────

def t_comparison : IO Unit := expectNoTH0026
  "function f(n: number): number { if (n !== 0) { return 1; } return 0; }"
def t_booleanParam : IO Unit := expectNoTH0026
  "function f(b: boolean): number { if (b) { return 1; } return 0; }"
-- literal `true` is a boolean subtype: `while (true)` stays admitted
def t_whileTrue : IO Unit := expectNoTH0026
  "function f(n: number): number { let k = n; while (true) { if (k <= 0) { break; } k -= 1; } return k; }"
def t_canonicalFor : IO Unit := expectNoTH0026
  "function f(n: number): number { let t = 0; for (let i = 0; i < 5; i++) { t += i; } return t; }"
def t_ternaryBoolean : IO Unit := expectNoTH0026
  "function f(n: number): string { return n > 0 ? \"pos\" : \"rest\"; }"
def t_negatedBoolean : IO Unit := expectNoTH0026
  "function f(b: boolean): number { if (!b) { return 1; } return 0; }"
def t_andBooleans : IO Unit := expectNoTH0026
  "function f(b: boolean, c: boolean): number { if (b && c) { return 1; } return 0; }"
def t_orBooleans : IO Unit := expectNoTH0026
  "function f(b: boolean, c: boolean): number { if (b || c) { return 1; } return 0; }"
def t_notComparison : IO Unit := expectNoTH0026
  "function f(n: number): number { if (!(n > 0)) { return 1; } return 0; }"

#eval t_ifNumber
#eval t_ifString
#eval t_whileNumber
#eval t_doWhileNumber
#eval t_forNumberTest
#eval t_ternaryNumber
#eval t_notNumber
#eval t_andNumberLeft
#eval t_orNumberRight
#eval t_orDefaultString
#eval t_comparison
#eval t_booleanParam
#eval t_whileTrue
#eval t_canonicalFor
#eval t_ternaryBoolean
#eval t_negatedBoolean
#eval t_andBooleans
#eval t_orBooleans
#eval t_notComparison
