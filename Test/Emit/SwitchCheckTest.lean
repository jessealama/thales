/-
  Test/Emit/SwitchCheckTest.lean
  Verifies TH0040 switch exhaustiveness on discriminated unions, and the
  #44 TH0041 classification: shapes the emitter has no lowering for
  (plain-identifier scrutinee, unresolvable binding, wrong field,
  non-returning arm) are rejected instead of silently dropped.
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

/-- A plain-identifier scrutinee is not TH0040's business (no TH0040), but
    since #44 it IS rejected as unlowerable (TH0041) — it used to be
    silently dropped from the emitted Lean. -/
def testUnknownDiscriminantNoFire : IO Unit := do
  let src := "
function f(s: string): number {
  switch (s) {
    case 'a': return 1;
    case 'b': return 2;
  }
}"
  expectNoCode src 40
  expectCode src 41

-- ── TH0041 classification (#44) ──

-- non-returning arm (break) on a proper discriminated dispatch
def testBreakArm41 : IO Unit := expectCode (unionTypeDecl ++ "
function f(s: S): number {
  switch (s.kind) {
    case 'a': break;
    case 'b': return 2;
    case 'c': return 3;
  }
  return 0;
}") 41

-- empty grouped case label: its body list does not return
def testGroupedCase41 : IO Unit := expectCode (unionTypeDecl ++ "
function f(s: S): number {
  switch (s.kind) {
    case 'a':
    case 'b': return 2;
    case 'c': return 3;
  }
}") 41

-- switch on a non-discriminator field
def testWrongField41 : IO Unit := expectCode ("type P = {kind: 'a', x: number} | {kind: 'b', x: number};
function f(p: P): number {
  switch (p.x) {
    case 'a': return 1;
    case 'b': return 2;
  }
}") 41

-- well-shaped discriminated dispatch: no TH0041
def testDiscriminatedOk41 : IO Unit := expectNoCode (unionTypeDecl ++ "
function f(s: S): number {
  switch (s.kind) {
    case 'a': return 1;
    case 'b': return 2;
    case 'c': return 3;
  }
}") 41

-- default arm whose body returns: accepted (lowers as the wildcard arm)
def testDefaultOk41 : IO Unit := expectNoCode (unionTypeDecl ++ "
function f(s: S): number {
  switch (s.kind) {
    case 'a': return 1;
    default: return 0;
  }
}") 41

-- missing arm with no default stays TH0040, not TH0041
def testNonExhaustiveNot41 : IO Unit := expectNoCode (unionTypeDecl ++ "
function f(s: S): number {
  switch (s.kind) {
    case 'a': return 1;
    case 'b': return 2;
  }
}") 41

-- switch on an ANNOTATED LOCAL: the binding threads through the
-- statement list, so the dispatch resolves and is accepted
def testAnnotatedLocalOk41 : IO Unit := expectNoCode (unionTypeDecl ++ "
function f(): number {
  const s: S = { kind: 'a' };
  switch (s.kind) {
    case 'a': return 1;
    case 'b': return 2;
    case 'c': return 3;
  }
}") 41

-- switch on an unannotated local: unresolvable scrutinee type
def testUnannotatedLocal41 : IO Unit := expectCode (unionTypeDecl ++ "
function f(): number {
  const s = { kind: 'a' };
  switch (s.kind) {
    case 'a': return 1;
    default: return 2;
  }
}") 41

-- VOID function: a fall-through (break) arm is fine — the unit arm the
-- emitter produces is the correct value, so no TH0041
def testVoidBreakArmOk41 : IO Unit := expectNoCode (unionTypeDecl ++ "
function f(s: S) {
  switch (s.kind) {
    case 'a':
      console.log('a');
      break;
    case 'b': return;
    case 'c': return;
  }
}") 41

#eval testNonExhaustive
#eval testExhaustiveOk
#eval testExhaustiveWithDefault
#eval testUnknownDiscriminantNoFire
#eval testBreakArm41
#eval testGroupedCase41
#eval testWrongField41
#eval testDiscriminatedOk41
#eval testDefaultOk41
#eval testNonExhaustiveNot41
#eval testAnnotatedLocalOk41
#eval testUnannotatedLocal41
#eval testVoidBreakArmOk41
