/-
  Test/Emit/LoopEscapeTest.lean
  Pins the #25 loop-shape flags on `MutationInfo`:
    * `hasLowerableLoop`     — the own body has a loop EscapeAnalysis admits
    * `hasUnloweredLoopShape` — the own body has a loop that poisons do-mode
  Both flags start `false`; lowerable loops set the first, everything
  else sets the second. `doModeLowerable` is false whenever the second is
  set.
-/
import Thales.Emit.EscapeAnalysis
import Thales.Parser.Native

open Thales.Emit.EscapeAnalysis
open Thales.Parser
open Thales.AST
open Thales.TypeCheck

/-- Parse `src`, find the first annotated function decl, analyze its body. -/
def analyzeFirstFuncLoop (src : String) : IO MutationInfo := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog =>
    for ts in prog.body do
      if let .annotatedFuncDecl _ _ _ params _ body _ _ _ _ := ts then
        return analyze (params.map (·.1)) body
    throw (IO.userError "no function decl found")

-- ── for-of with accumulation: lowerable ──────────────────────────────────────
-- for-of over array param with += accumulation → lowerable, do-mode ok
def t1 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(xs: number[], t: number): number { for (const x of xs) { t += x; } return t; }"
  unless info.hasLowerableLoop do
    throw (IO.userError s!"expected hasLowerableLoop, got false")
  if info.hasUnloweredLoopShape then
    throw (IO.userError s!"expected !hasUnloweredLoopShape, got true")
  unless info.doModeLowerable do
    throw (IO.userError s!"expected doModeLowerable, got false")

-- ── while loop: poisons do-mode ───────────────────────────────────────────────
def t2 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(x: number): number { let n = 0; while (n < x) { n += 1; } return n; }"
  if info.hasLowerableLoop then
    throw (IO.userError s!"expected !hasLowerableLoop, got true")
  unless info.hasUnloweredLoopShape do
    throw (IO.userError s!"expected hasUnloweredLoopShape, got false")
  if info.doModeLowerable then
    throw (IO.userError s!"expected !doModeLowerable, got true")

-- ── for-of with loop-var reassignment: poisons do-mode ───────────────────────
def t3 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(xs: number[]): number { for (let x of xs) { x = x + 1; } return 0; }"
  unless info.hasUnloweredLoopShape do
    throw (IO.userError s!"expected hasUnloweredLoopShape (loop var reassigned), got false")
  if info.doModeLowerable then
    throw (IO.userError s!"expected !doModeLowerable (loop var reassigned), got true")

-- ── canonical for with bound-ident mutation: poisons do-mode ─────────────────
-- for (let i = 0; i < xs.length; i++) { xs = xs; }  xs is a param → mutated
def t4 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(xs: number[]): number { let t = 0; for (let i = 0; i < xs.length; i++) { xs = xs; } return t; }"
  unless info.hasUnloweredLoopShape do
    throw (IO.userError s!"expected hasUnloweredLoopShape (bound ident mutated), got false")
  if info.doModeLowerable then
    throw (IO.userError s!"expected !doModeLowerable (bound ident mutated), got true")

-- ── labeled break inside for-of: poisons do-mode ─────────────────────────────
-- The loop sits under a labeledStmt; the body contains a labeled break.
def t5 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(xs: number[]): number { outer: for (const x of xs) { break outer; } return 0; }"
  unless info.hasUnloweredLoopShape do
    throw (IO.userError s!"expected hasUnloweredLoopShape (labeled break), got false")
  if info.doModeLowerable then
    throw (IO.userError s!"expected !doModeLowerable (labeled break), got true")

-- ── canonical for with literal bound: lowerable ───────────────────────────────
def t6 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(): number { let t = 0; for (let i = 0; i < 10; i++) { t += i; } return t; }"
  unless info.hasLowerableLoop do
    throw (IO.userError s!"expected hasLowerableLoop (literal bound), got false")
  if info.hasUnloweredLoopShape then
    throw (IO.userError s!"expected !hasUnloweredLoopShape (literal bound), got true")
  unless info.doModeLowerable do
    throw (IO.userError s!"expected doModeLowerable (literal bound), got false")

-- ── nested for-of inside for-of (both admitted): lowerable ────────────────────
def t7 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(xs: number[][], t: number): number { for (const row of xs) { for (const x of row) { t += x; } } return t; }"
  unless info.hasLowerableLoop do
    throw (IO.userError s!"expected hasLowerableLoop (nested for-of), got false")
  if info.hasUnloweredLoopShape then
    throw (IO.userError s!"expected !hasUnloweredLoopShape (nested for-of), got true")

-- ── for-of with inner while: poisons do-mode ─────────────────────────────────
def t8 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(xs: number[]): number { let t = 0; for (const x of xs) { while (t < x) { t += 1; } } return t; }"
  unless info.hasUnloweredLoopShape do
    throw (IO.userError s!"expected hasUnloweredLoopShape (inner while), got false")
  if info.doModeLowerable then
    throw (IO.userError s!"expected !doModeLowerable (inner while), got true")

-- ── no loops: both flags false (regression guard) ────────────────────────────
def t9 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(x: number): number { return x + 1; }"
  if info.hasLowerableLoop then
    throw (IO.userError s!"expected !hasLowerableLoop (no loops), got true")
  if info.hasUnloweredLoopShape then
    throw (IO.userError s!"expected !hasUnloweredLoopShape (no loops), got true")

#eval t1
#eval t2
#eval t3
#eval t4
#eval t5
#eval t6
#eval t7
#eval t8
#eval t9
