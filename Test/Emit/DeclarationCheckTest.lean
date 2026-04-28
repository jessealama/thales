/-
  Test/Emit/DeclarationCheckTest.lean
  Verifies TH0030 (class) and TH0031 (inheritance).
-/
import Thales.Emit.SubsetCheck
import Thales.Parser.Native

open Thales.Emit Thales.Parser Thales.TypeCheck

def expectDeclCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    unless diags.any (·.thalesCode? = some code) do
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"expected TH{code}, got: {fmt}")

def testClassDecl : IO Unit :=
  expectDeclCode "class C { x: number = 1; }" 30

def testClassExpr : IO Unit :=
  expectDeclCode "const C = class { y: number = 2; };" 30

def testExtends : IO Unit := do
  let src := "class A {} class B extends A { z: number = 3; }"
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    -- Both TH0030 (for each class) and TH0031 (for extends) should fire.
    unless diags.any (·.thalesCode? = some 30) do
      throw (IO.userError "expected TH0030 (class not supported)")
    unless diags.any (·.thalesCode? = some 31) do
      throw (IO.userError "expected TH0031 (extends not supported)")

#eval testClassDecl
#eval testClassExpr
#eval testExtends
