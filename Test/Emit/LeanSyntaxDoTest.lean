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

#eval t1
#eval t2
#eval t3
#eval t4
