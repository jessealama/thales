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

-- ── TH0032 shadowing (#45) ──

def expectNoDeclCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    if diags.any (·.thalesCode? = some code) then
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"did not expect TH{code}, got: {fmt}")

-- bare-block shadow of a function-level const
def testBareBlockShadow : IO Unit := expectDeclCode
  "function f(): number { const n = 0; { const n = 1; } return n; }" 32
-- if-branch shadow (the pure path appends the continuation into branches)
def testIfBranchShadow : IO Unit := expectDeclCode
  "function f(c: boolean): number { const n = 0; if (c) { const n = 1; } return n; }" 32
-- let shadowing a parameter from a nested block
def testParamShadow : IO Unit := expectDeclCode
  "function f(x: number): number { { let x = 1; return x; } }" 32
-- arrow parameters and bodies are fresh scopes: no TH0032
def testArrowParamNoShadow : IO Unit := expectNoDeclCode
  "function f(): number { const y = 1; const g = (y: number): number => y + 1; return g(y); }" 32
def testArrowBodyNoShadow : IO Unit := expectNoDeclCode
  "function f(): number { const y = 1; const g = (): number => { const y = 2; return y; }; return g() + y; }" 32
-- `var` re-declaration is the same function-scoped binding: no TH0032
def testVarRedeclNoShadow : IO Unit := expectNoDeclCode
  "function f(): number { var n = 0; { var n = 1; } return n; }" 32
-- sibling scopes don't shadow each other
def testSiblingBlocksNoShadow : IO Unit := expectNoDeclCode
  "function f(c: boolean): number { if (c) { const k = 1; return k; } const k = 2; return k; }" 32

#eval testClassDecl
#eval testClassExpr
#eval testExtends
#eval testBareBlockShadow
#eval testIfBranchShadow
#eval testParamShadow
#eval testArrowParamNoShadow
#eval testArrowBodyNoShadow
#eval testVarRedeclNoShadow
#eval testSiblingBlocksNoShadow
