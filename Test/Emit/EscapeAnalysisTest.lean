/-
  Test/Emit/EscapeAnalysisTest.lean
  Pins the #24 eligibility rule: a binding is mutable-eligible iff every
  reference to it occurs in the declaring function's own body — no
  reference from any nested function/arrow — and it is a parameter or an
  initialized `let`, and it is not entangled with narrowing tests.
-/
import Thales.Emit.EscapeAnalysis
import Thales.Parser.Native

open Thales.Emit.EscapeAnalysis
open Thales.Parser
open Thales.AST
open Thales.TypeCheck

/-- Parse `src`, find the first annotated function decl, analyze its body. -/
def analyzeFirstFunc (src : String) : IO MutationInfo := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog =>
    for ts in prog.body do
      if let .annotatedFuncDecl _ _ _ params _ body _ _ _ _ := ts then
        return analyze (params.map (·.1)) body
    throw (IO.userError "no function decl found")

def expectEligible (src : String) (name : String) (expected : Bool) : IO Unit := do
  let info ← analyzeFirstFunc src
  let got := info.eligible name
  unless got == expected do
    throw (IO.userError s!"eligible '{name}' = {got}, expected {expected} in: {src}")

-- straight-line local mutation: eligible
def t1 : IO Unit := expectEligible
  "function f(): number { let n = 0; n = 1; return n; }" "n" true
-- read from a nested arrow: NOT eligible
def t2 : IO Unit := expectEligible
  "function f(): number { let n = 0; const g = () => n; n = 1; return g(); }" "n" false
-- write from a nested arrow: NOT eligible
def t3 : IO Unit := expectEligible
  "function f(): number { let n = 0; const g = () => { n = 1; }; g(); return n; }" "n" false
-- parameter: eligible
def t4 : IO Unit := expectEligible
  "function f(x: number): number { x = x + 1; return x; }" "x" true
-- let without initializer: NOT eligible
def t5 : IO Unit := expectEligible
  "function f(): number { let n: number; n = 1; return n; }" "n" false
-- arrow not mentioning the mutated var does not disqualify it
def t6 : IO Unit := expectEligible
  "function f(): number { let n = 0; const g = (y: number) => y + 1; n = 1; return g(n); }" "n" true
-- null-tested var: NOT eligible (conservative v1 guard) …
def t7 : IO Unit := expectEligible
  "function f(x: string | null): number { let n = 0; if (x === null) { n = 1; } return n; }" "x" false
-- … but the merely-branch-assigned var in the same source IS eligible
def t7b : IO Unit := expectEligible
  "function f(x: string | null): number { let n = 0; if (x === null) { n = 1; } return n; }" "n" true
-- refinement-predicate-tested var (call with single ident arg in condition): NOT eligible
def t7c : IO Unit := expectEligible
  "function f(x: number): number { x = 0; if (isInteger(x)) { return 1; } return x; }" "x" false

-- mutated-set sanity: n++ and n += 1 both count as mutation sites
def t8 : IO Unit := do
  let info ← analyzeFirstFunc "function f(): number { let n = 0; n++; n += 1; return n; }"
  unless info.mutated.contains "n" do throw (IO.userError "n not in mutated")

-- const declarations are recorded as consts, not initializedLets
def t9 : IO Unit := do
  let info ← analyzeFirstFunc "function f(): number { const c = 1; let n = 0; n = c; return n; }"
  unless info.consts.contains "c" do throw (IO.userError "c not in consts")
  if info.initializedLets.contains "c" then throw (IO.userError "c wrongly in initializedLets")

-- switch shapes: all-arms-return is lowerable; a non-returning arm or a
-- `default` arm is not (do-mode would need post-switch join emission)
def expectUnloweredSwitch (src : String) (expected : Bool) : IO Unit := do
  let info ← analyzeFirstFunc src
  unless info.hasUnloweredSwitchShape == expected do
    throw (IO.userError s!"hasUnloweredSwitchShape = {!expected}, expected {expected}")

def t10 : IO Unit := expectUnloweredSwitch
  "function f(x: string): number { let n = 0; switch (x) { case \"a\": n = 1; return n; case \"b\": return 2; } return n; }"
  false
def t11 : IO Unit := expectUnloweredSwitch
  "function f(x: string): number { let n = 0; switch (x) { case \"a\": n = 1; break; case \"b\": return 2; } return n; }"
  true
def t12 : IO Unit := expectUnloweredSwitch
  "function f(x: string): number { let n = 0; switch (x) { case \"a\": return 1; default: return 2; } }"
  true

#eval t1
#eval t2
#eval t3
#eval t4
#eval t5
#eval t6
#eval t7
#eval t7b
#eval t7c
#eval t8
#eval t9
#eval t10
#eval t11
#eval t12
