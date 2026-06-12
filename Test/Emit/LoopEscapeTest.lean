/-
  Test/Emit/LoopEscapeTest.lean
  Pins the #25/#26 loop-shape flags on `MutationInfo`:
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

-- ── while loop: lowerable (#26) ──────────────────────────────────────────────
def t2 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(x: number): number { let n = 0; while (n < x) { n += 1; } return n; }"
  unless info.hasLowerableLoop do
    throw (IO.userError s!"expected hasLowerableLoop (while, #26), got false")
  if info.hasUnloweredLoopShape then
    throw (IO.userError s!"expected !hasUnloweredLoopShape (while, #26), got true")
  unless info.doModeLowerable do
    throw (IO.userError s!"expected doModeLowerable (while, #26), got false")

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

-- ── for-of with inner while: both lowerable (#26) ────────────────────────────
def t8 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(xs: number[]): number { let t = 0; for (const x of xs) { while (t < x) { t += 1; } } return t; }"
  unless info.hasLowerableLoop do
    throw (IO.userError s!"expected hasLowerableLoop (inner while, #26), got false")
  if info.hasUnloweredLoopShape then
    throw (IO.userError s!"expected !hasUnloweredLoopShape (inner while, #26), got true")

-- ── no loops: both flags false (regression guard) ────────────────────────────
def t9 : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(x: number): number { return x + 1; }"
  if info.hasLowerableLoop then
    throw (IO.userError s!"expected !hasLowerableLoop (no loops), got true")
  if info.hasUnloweredLoopShape then
    throw (IO.userError s!"expected !hasUnloweredLoopShape (no loops), got true")

-- ── shadowed loop var with body mutation: poisons do-mode ────────────────────
-- Outer `i` is mutated before the loop; the canonical-for declares a shadowing
-- `i`; the body further mutates it. The before/after diff is unreliable
-- (both share the key "i"), so any post-body visibility of `i` in `mutated`
-- poisons. This guards the latent miscompile where `bodyMutatedV = false`
-- because `vMutatedBeforeBody = true`.
def t_shadowedLoopVar : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(xs: number[]): number { let i = 0; i = 5; for (let i = 0; i < xs.length; i++) { i = i + 2; } return i; }"
  unless info.hasUnloweredLoopShape do
    throw (IO.userError "expected hasUnloweredLoopShape for shadowed mutated loop var")
  if info.doModeLowerable then
    throw (IO.userError "expected !doModeLowerable for shadowed mutated loop var")

-- ── shadowed loop var, clean body: conservatively poisons ────────────────────
-- Outer `i` is mutated before the loop; the canonical-for declares a shadowing
-- `i`; the body is clean (no mutation of `i`). After the fix, the outer `i`'s
-- pre-loop mutation is visible in `accAfterBody.mutated`, which poisons.
-- This is a false positive but is documented and acceptable — sound conservatism.
def t_shadowedLoopVarCleanBody : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(xs: number[]): number { let i = 0; i = 5; for (let i = 0; i < xs.length; i++) { } return i; }"
  unless info.hasUnloweredLoopShape do
    throw (IO.userError "expected hasUnloweredLoopShape (conservative: outer same-named mutated var)")
  if info.doModeLowerable then
    throw (IO.userError "expected !doModeLowerable (conservative: outer same-named mutated var)")

-- ── labeled loop (no labeled break) → poisons do-mode ───────────────────────
-- A label wrapping a for-of, even with no labeled break/continue in the body,
-- must set hasUnloweredLoopShape: `emitBodyDo` has no labeledStmt arm, so the
-- label would fall through to the loud marker on any accepted program.
def t_labeledLoopNoBreak : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(xs: number[]): number { let t = 0; outer: for (const x of xs) { t += x; } return t; }"
  unless info.hasUnloweredLoopShape do
    throw (IO.userError "expected hasUnloweredLoopShape (labeled loop, no break), got false")
  if info.doModeLowerable then
    throw (IO.userError "expected !doModeLowerable (labeled loop, no break), got true")

-- ── #26: do-while is lowerable ───────────────────────────────────────────────
def t_doWhile : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(n: number): number { let s = 0; do { s += 1; n -= 1; } while (n > 0); return s; }"
  unless info.hasLowerableLoop do
    throw (IO.userError "expected hasLowerableLoop (do-while), got false")
  if info.hasUnloweredLoopShape then
    throw (IO.userError "expected !hasUnloweredLoopShape (do-while), got true")

-- ── #26: do-while with loop-level continue poisons ──────────────────────────
-- TS `continue` jumps to the test; `repeat … until` re-enters the body
-- without checking it, so the shape cannot lower.
def t_doWhileContinue : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(n: number): number { do { if (n > 0) { continue; } } while (n > 0); return n; }"
  unless info.hasUnloweredLoopShape do
    throw (IO.userError "expected hasUnloweredLoopShape (do-while continue), got false")
  if info.doModeLowerable then
    throw (IO.userError "expected !doModeLowerable (do-while continue), got true")

-- ── #26: while with continue is fine (Lean's while re-checks the test) ──────
def t_whileContinue : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(n: number): number { let s = 0; while (s < n) { s += 1; if (s > 2) { continue; } } return s; }"
  unless info.hasLowerableLoop do
    throw (IO.userError "expected hasLowerableLoop (while continue), got false")
  if info.hasUnloweredLoopShape then
    throw (IO.userError "expected !hasUnloweredLoopShape (while continue), got true")

-- ── #26: while with labeled break poisons ────────────────────────────────────
def t_whileLabeledBreak : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(n: number): number { outer: while (n > 0) { break outer; } return n; }"
  unless info.hasUnloweredLoopShape do
    throw (IO.userError "expected hasUnloweredLoopShape (while labeled break), got false")

-- ── #26: non-canonical for (compound step) is lowerable via while-desugar ───
def t_generalFor : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(n: number): number { let t = 0; for (let i = n; i > 0; i -= 2) { t += i; } return t; }"
  unless info.hasLowerableLoop do
    throw (IO.userError "expected hasLowerableLoop (general for, #26), got false")
  if info.hasUnloweredLoopShape then
    throw (IO.userError "expected !hasUnloweredLoopShape (general for, #26), got true")

-- ── #26: general for + loop-level continue (update would be skipped) ────────
def t_generalForContinue : IO Unit := do
  let info ← analyzeFirstFuncLoop
    "function f(n: number): number { let t = 0; for (let i = n; i > 0; i -= 2) { if (i > 4) { continue; } t += i; } return t; }"
  unless info.hasUnloweredLoopShape do
    throw (IO.userError "expected hasUnloweredLoopShape (general for continue), got false")

#eval t1
#eval t2
#eval t3
#eval t4
#eval t5
#eval t6
#eval t7
#eval t8
#eval t9
#eval t_shadowedLoopVar
#eval t_shadowedLoopVarCleanBody
#eval t_labeledLoopNoBreak
#eval t_doWhile
#eval t_doWhileContinue
#eval t_whileContinue
#eval t_whileLabeledBreak
#eval t_generalFor
#eval t_generalForContinue
