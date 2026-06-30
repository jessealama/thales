/-
  Test/Emit/ControlFlowCheckTest.lean
  Verifies TH0010 (loops), TH0012 (async) via subsetCheck. TH0060
  (unannotated throw) is verified separately via throwsAnnotationCheck
  (see testThrow).
-/
import Thales.Emit.SubsetCheck
import Thales.TypeCheck.Check
import Thales.Parser.Native

open Thales.Emit Thales.Parser Thales.TypeCheck

def expectCFCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    unless diags.any (·.thalesCode? = some code) do
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"expected TH{code}, got: {fmt}")

/-- Verify that the given code does NOT fire (the construct is in-subset). -/
def expectNoCFCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    if diags.any (·.thalesCode? = some code) then
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"expected no TH{code}, got: {fmt}")

/-- Verify that throwsAnnotationCheck (TH0060) fires for the given source. -/
def expectThrowsCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := throwsAnnotationCheck prog
    unless diags.any (·.thalesCode? = some code) do
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"expected TH{code}, got: {fmt}")

-- Module-level loops are now in-subset, lowered into the `main` IO do-block
-- on the same terms as a function body (#49) — no TH0010. `for…in` stays out
-- of subset (no lowering), so it still draws TH0010.
def testForLoop : IO Unit := expectNoCFCode "for (let i = 0; i < 3; i++) {}" 10
def testForOfLoop : IO Unit := expectNoCFCode "for (const x of [1,2,3]) {}" 10
def testForInLoop : IO Unit := expectCFCode "for (const k in {a:1}) {}" 10
def testWhileLoop : IO Unit := expectNoCFCode "while (true) {}" 10
def testDoWhileLoop : IO Unit := expectNoCFCode "do {} while (false);" 10

-- TH0060 fires only for throws inside an `annotatedFuncDecl` whose
-- `throwsAnn = .absent`, so the test source wraps the throw in a function.
def testThrow : IO Unit :=
  expectThrowsCode "function f(): number { throw new Error('x'); }" 60

-- try/catch behavior is tested via the conformance harness (example 32);
-- `finally` is out of scope for v1.0.

def testAsyncFunction : IO Unit := expectCFCode "async function f() {}" 12
def testAwaitExpr : IO Unit := expectCFCode "async function f() { return await g(); }" 12
def testAsyncArrow : IO Unit := expectCFCode "const f = async () => 1;" 12

#eval testForLoop
#eval testForOfLoop
#eval testForInLoop
#eval testWhileLoop
#eval testDoWhileLoop
#eval testThrow
#eval testAsyncFunction
#eval testAwaitExpr
#eval testAsyncArrow
