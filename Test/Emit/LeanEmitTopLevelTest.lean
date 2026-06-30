/-
  Test/Emit/LeanEmitTopLevelTest.lean
  Exercises the top-level `def main` IO do-block: the `ioDo`/`doExpr` IR
  rendering, and the `emitIOBodyDo`/partition lowering of module-level
  mutation, loops, and `console.log` (#49).
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Emit.LeanSyntax
open Thales.Parser

-- `ioDo` renders a plain `do` block; `doExpr` renders a bare action.
/-- info: do
  (consoleLog x)
  (IO.println "hi") -/
#guard_msgs in
#eval IO.println (renderExpr (.ioDo [
  .doExpr (.app (.var "consoleLog") [.var "x"]),
  .doExpr (.app (.var "IO.println") [.str "hi"]) ]))

/-- Parse a top-level program, emit it, and assert every needle appears. -/
def expectEmitTop (src moduleName : String) (needles : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog moduleName
    for n in needles do
      unless (out.splitOn n).length ≥ 2 do
        throw (IO.userError s!"missing '{n}' in:\n{out}")

/-- Assert a needle does NOT appear in the emitted output. -/
def expectEmitTopAbsent (src moduleName : String) (needle : String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog moduleName
    if (out.splitOn needle).length ≥ 2 then
      throw (IO.userError s!"unexpected '{needle}' in:\n{out}")

-- A mutated top-level `let` becomes a `let mut` inside `def main`; a plain `=`
-- reassignment becomes `:=`.
def testTopLevelMutLet : IO Unit :=
  expectEmitTop "let total = 0; total = total + 1; console.log(total);" "M"
    ["def main : IO Unit", "let mut total", "total := (total +", "consoleLog total"]

-- A for-of over an array literal becomes `for x in … do`; the `+=` body
-- becomes a `:=` reassignment.
def testTopLevelForOf : IO Unit :=
  expectEmitTop "let total = 0; for (const x of [1, 2, 3]) { total += x; } console.log(total);" "M"
    ["let mut total", "for x in", "total := (total + x)", "consoleLog total"]

-- A canonical `for` becomes `for i in [0:…] do`.
def testTopLevelCanonicalFor : IO Unit :=
  expectEmitTop "for (let i = 0; i < 3; i++) { console.log(i); }" "M"
    ["def main : IO Unit", "for i in", "consoleLog"]

-- A bare top-level `console.log` is preserved as a `consoleLog` action inside
-- `main` (not dropped, unlike the pure function-body path).
def testTopLevelConsoleLog : IO Unit :=
  expectEmitTop "console.log(42);" "M"
    ["def main : IO Unit", "consoleLog", "#eval main"]

-- A non-mutated `const` is hoisted as a top-level `def`, NOT lowered into
-- `main` as a `let`.
def testTopLevelConstHoisted : IO Unit :=
  expectEmitTop "const base = 3; console.log(base);" "M"
    ["def base", "def main : IO Unit", "consoleLog base"]

def testTopLevelConstNotInMain : IO Unit :=
  expectEmitTopAbsent "const base = 3; console.log(base);" "M" "let base"

#eval testTopLevelMutLet
#eval testTopLevelForOf
#eval testTopLevelCanonicalFor
#eval testTopLevelConsoleLog
#eval testTopLevelConstHoisted
#eval testTopLevelConstNotInMain
