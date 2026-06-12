/-
  Test/Emit/LeanSyntaxDoTest.lean
  Golden tests for the LDoStmt / Id.run do rendering (#24). The expected
  strings pin the renderer's actual conventions: binOp always
  parenthesizes, floats render with full precision (`0.000000`), and
  nested do-blocks indent by two spaces per level.
-/
import Thales.Emit.LeanSyntax

open Thales.Emit.LeanSyntax

private def expectRender (got expected : String) : IO Unit := do
  unless got == expected do
    throw (IO.userError s!"render mismatch:\n---got---\n{got}\n---want---\n{expected}")

def counterBody : LExpr :=
  .idRunDo [
    .letMut "n" (some (.const "Float")) (.float 0.0),
    .assign "n" (.binOp "+" (.var "n") (.float 1.0)),
    .ifDo (.binOp "==" (.var "n") (.float 1.0))
      [.assign "n" (.binOp "+" (.var "n") (.float 2.0))] [],
    .ret (.var "n")
  ]

def counterExpected : String :=
  "Id.run do\n" ++
  "  let mut n : Float := 0.000000\n" ++
  "  n := (n + 1.000000)\n" ++
  "  if (n == 1.000000) then\n" ++
  "    n := (n + 2.000000)\n" ++
  "  return n"

def t1 : IO Unit := expectRender (renderExpr counterBody) counterExpected

-- if/else with both branches, unannotated let mut, pure let in do
def branchBody : LExpr :=
  .idRunDo [
    .letMut "m" none (.var "x"),
    .letPure "limit" none (.float 10.0),
    .ifDo (.binOp ">" (.var "m") (.var "limit"))
      [.ret (.var "limit")]
      [.assign "m" (.binOp "+" (.var "m") (.float 1.0))],
    .ret (.var "m")
  ]

def branchExpected : String :=
  "Id.run do\n" ++
  "  let mut m := x\n" ++
  "  let limit := 10.000000\n" ++
  "  if (m > limit) then\n" ++
  "    return limit\n" ++
  "  else\n" ++
  "    m := (m + 1.000000)\n" ++
  "  return m"

def t2 : IO Unit := expectRender (renderExpr branchBody) branchExpected

-- empty branch renders `pure ()`; matchDo arms hold statement lists
def emptyThen : LExpr :=
  .idRunDo [
    .ifDo (.var "c") [] [.assign "n" (.float 0.0)],
    .ret (.var "n")
  ]

def emptyThenExpected : String :=
  "Id.run do\n" ++
  "  if c then\n" ++
  "    pure ()\n" ++
  "  else\n" ++
  "    n := 0.000000\n" ++
  "  return n"

def t3 : IO Unit := expectRender (renderExpr emptyThen) emptyThenExpected

def matchBody : LExpr :=
  .idRunDo [
    .letMut "area" none (.float 0.0),
    .matchDo (.var "shape") [
      (.ctor "circle" [.var "r"], [
        .assign "area" (.binOp "*" (.var "r") (.var "r")),
        .ret (.var "area")
      ]),
      (.wildcard, [.ret (.float 0.0)])
    ]
  ]

def matchExpected : String :=
  "Id.run do\n" ++
  "  let mut area := 0.000000\n" ++
  "  match shape with\n" ++
  "  | .circle r =>\n" ++
  "    area := (r * r)\n" ++
  "    return area\n" ++
  "  | _ =>\n" ++
  "    return 0.000000"

def t4 : IO Unit := expectRender (renderExpr matchBody) matchExpected

-- forDo / breakDo / continueDo / rangeTo (#25) ----------------------------

-- t5: idRunDo with a forDo loop (letMut + for + ret)
def forLoopBody : LExpr :=
  .idRunDo [
    .letMut "t" none (.float 0.0),
    .forDo "x" (.var "xs") [
      .assign "t" (.binOp "+" (.var "t") (.var "x"))
    ],
    .ret (.var "t")
  ]

def forLoopExpected : String :=
  "Id.run do\n" ++
  "  let mut t := 0.000000\n" ++
  "  for x in xs do\n" ++
  "    t := (t + x)\n" ++
  "  return t"

def t5 : IO Unit := expectRender (renderExpr forLoopBody) forLoopExpected

-- t6: forDo with rangeTo iter and breakDo body
def rangeBreakStmt : String :=
  renderDoStmt (.forDo "i" (.rangeTo (.proj (.var "xs") "length")) [.breakDo])

def rangeBreakExpected : String :=
  "for i in [0:xs.length] do\n" ++
  "  break"

def t6 : IO Unit := expectRender rangeBreakStmt rangeBreakExpected

-- t7: continueDo renders "continue" inside a forDo body
def continueStmt : String :=
  renderDoStmt (.forDo "i" (.var "arr") [.continueDo])

def continueExpected : String :=
  "for i in arr do\n" ++
  "  continue"

def t7 : IO Unit := expectRender continueStmt continueExpected

-- t8: nested forDo — indentation doubles
def nestedForStmt : String :=
  renderDoStmt (.forDo "i" (.var "outer") [
    .forDo "j" (.var "inner") [
      .assign "s" (.var "s")
    ]
  ])

def nestedForExpected : String :=
  "for i in outer do\n" ++
  "  for j in inner do\n" ++
  "    s := s"

def t8 : IO Unit := expectRender nestedForStmt nestedForExpected

-- t9: doStmtsTerminate — forDo alone is false; forDo then ret is true
def t9 : IO Unit := do
  unless !doStmtsTerminate [.forDo "i" (.var "xs") [.ret (.var "i")]] do
    throw (IO.userError "forDo alone should not terminate")
  unless doStmtsTerminate [.forDo "i" (.var "xs") [], .ret (.var "x")] do
    throw (IO.userError "forDo then ret should terminate")

-- t10: empty forDo body renders "pure ()" as the body
def emptyForStmt : String :=
  renderDoStmt (.forDo "i" (.var "xs") [])

def emptyForExpected : String :=
  "for i in xs do\n" ++
  "  pure ()"

def t10 : IO Unit := expectRender emptyForStmt emptyForExpected

-- whileDo / repeatUntilDo (#26) ---------------------------------------------

-- t11: whileDo renders `while c do` with an indented body
def whileStmtRender : String :=
  renderDoStmt (.whileDo (.binOp "<" (.var "pad") (.var "len")) [
    .assign "pad" (.binOp "+" (.var "ch") (.var "pad"))
  ])

def whileExpected : String :=
  "while (pad < len) do\n" ++
  "  pad := (ch + pad)"

def t11 : IO Unit := expectRender whileStmtRender whileExpected

-- t12: repeatUntilDo renders `repeat`, indented body, dedented `until c`
def repeatStmtRender : String :=
  renderDoStmt (.repeatUntilDo [
    .assign "n" (.binOp "-" (.var "n") (.int 1))
  ] (.app (.var "not") [.binOp ">" (.var "n") (.int 0)]))

def repeatExpected : String :=
  "repeat\n" ++
  "  n := (n - 1)\n" ++
  "until (not ((n > 0)))"

def t12 : IO Unit := expectRender repeatStmtRender repeatExpected

-- t13: doStmtsTerminate — while/repeatUntil alone are false; with trailing
-- ret the list terminates
def t13 : IO Unit := do
  unless !doStmtsTerminate [.whileDo (.bool true) [.ret (.var "x")]] do
    throw (IO.userError "whileDo alone should not terminate")
  unless doStmtsTerminate [.whileDo (.bool true) [], .ret (.var "x")] do
    throw (IO.userError "whileDo then ret should terminate")
  unless !doStmtsTerminate [.repeatUntilDo [.ret (.var "x")] (.bool true)] do
    throw (IO.userError "repeatUntilDo alone should not terminate")

-- t14: empty whileDo body renders "pure ()" (valid Lean)
def t14 : IO Unit := expectRender
  (renderDoStmt (.whileDo (.bool true) []))
  ("while true do\n" ++ "  pure ()")

#eval t1
#eval t2
#eval t3
#eval t4
#eval t5
#eval t6
#eval t7
#eval t8
#eval t9
#eval t10
#eval t11
#eval t12
#eval t13
#eval t14
