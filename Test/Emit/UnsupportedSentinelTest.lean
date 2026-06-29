/-
  Test/Emit/UnsupportedSentinelTest.lean
  The structural sentinel (#30): LModule.unsupportedReasons detects any
  LExpr.unsupported placeholder, so Main's TH9005 gate can refuse to emit.
-/
import Thales.Emit.LeanSyntax

open Thales.Emit.LeanSyntax

-- A module whose single def body contains an `.unsupported` node, nested under
-- a namespace and an `ite` to exercise the recursive traversal.
private def dirtyModule : LModule :=
  { imports := ["Thales.TS.Runtime"]
    opens := ["Thales.TS"]
    decls :=
      [ .namespace_ "M"
          [ .def_ "f" [] [("x", .const "Int")] (.const "Int")
              (.ite (.bool true) (.unsupported "regex literal") (.var "x")) false ] ] }

-- A clean module with no placeholder.
private def cleanModule : LModule :=
  { imports := ["Thales.TS.Runtime"]
    opens := ["Thales.TS"]
    decls :=
      [ .namespace_ "M"
          [ .def_ "g" [] [("x", .const "Int")] (.const "Int") (.var "x") false ] ] }

def testDetectsUnsupported : IO Unit := do
  let reasons := dirtyModule.unsupportedReasons
  unless reasons == ["regex literal"] do
    throw (IO.userError s!"expected [\"regex literal\"], got {reasons}")

def testCleanModuleHasNone : IO Unit := do
  let reasons := cleanModule.unsupportedReasons
  unless reasons == [] do
    throw (IO.userError s!"expected [], got {reasons}")

#eval testDetectsUnsupported
#eval testCleanModuleHasNone
