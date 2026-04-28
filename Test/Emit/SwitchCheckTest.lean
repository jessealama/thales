/-
  Test/Emit/SwitchCheckTest.lean
  Verifies TH0040 switch exhaustiveness on discriminated unions.
-/
import Thales.Emit.SubsetCheck
import Thales.Parser.Native

open Thales.Emit Thales.Parser

def expectCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    unless diags.any (·.thalesCode? = some code) do
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"expected TH{code}, got: {fmt}")

def expectNoCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    if diags.any (·.thalesCode? = some code) then
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"did not expect TH{code}, got: {fmt}")

def unionTypeDecl : String :=
  "type S = {kind: 'a'} | {kind: 'b'} | {kind: 'c'};"

def testNonExhaustive : IO Unit := expectCode (unionTypeDecl ++ "
function f(s: S): number {
  switch (s.kind) {
    case 'a': return 1;
    case 'b': return 2;
  }
}") 40

def testExhaustiveOk : IO Unit := expectNoCode (unionTypeDecl ++ "
function f(s: S): number {
  switch (s.kind) {
    case 'a': return 1;
    case 'b': return 2;
    case 'c': return 3;
  }
}") 40

def testExhaustiveWithDefault : IO Unit := expectNoCode (unionTypeDecl ++ "
function f(s: S): number {
  switch (s.kind) {
    case 'a': return 1;
    default: return 0;
  }
}") 40

/-- For v1, if the type is not declared as a union or we can't see it,
    no TH0040 fires. This is a safe-default test. -/
def testUnknownDiscriminantNoFire : IO Unit := expectNoCode "
function f(s: string): number {
  switch (s) {
    case 'a': return 1;
    case 'b': return 2;
  }
}" 40

#eval testNonExhaustive
#eval testExhaustiveOk
#eval testExhaustiveWithDefault
#eval testUnknownDiscriminantNoFire
