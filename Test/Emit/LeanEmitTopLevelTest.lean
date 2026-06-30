import Thales.Emit.LeanSyntax

open Thales.Emit.LeanSyntax

-- `ioDo` renders a plain `do` block; `doExpr` renders a bare action.
/-- info: do
  (consoleLog x)
  (IO.println "hi") -/
#guard_msgs in
#eval IO.println (renderExpr (.ioDo [
  .doExpr (.app (.var "consoleLog") [.var "x"]),
  .doExpr (.app (.var "IO.println") [.str "hi"]) ]))
