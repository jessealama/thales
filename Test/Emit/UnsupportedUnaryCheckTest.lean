/-
  Test/Emit/UnsupportedUnaryCheckTest.lean
  Verifies the value-level unary/literal rejections that keep the emitter from
  ever lowering a construct it has no Lean form for:
    - TH0091: regex literal
    - TH0092: `typeof` / `void` / `delete`
  The `typeof` cases include guard positions (`if (typeof x === …)`,
  `switch (typeof x)`). Those were once carved out as "narrowing consumes them,"
  but the emitter cannot lower `typeof` in any position, so a carve-out let an
  accepted program trip the TH9005 emit gate (#30). These assertions lock the
  carve-out out: `typeof` must be rejected wherever it appears.
-/
import Thales.Emit.SubsetCheck
import Thales.Parser.Native

open Thales.Emit Thales.Parser Thales.TypeCheck

/-- Assert `subsetCheck` reports `code` for `src`. Uses `.any`, so it tolerates
    additional codes (e.g. `switch (typeof x)` also raises TH0041). -/
def expectUnaryCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    unless diags.any (·.thalesCode? = some code) do
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"expected TH{code}, got: {fmt}")

-- TH0091: regex literal in value position.
def testRegexLiteral : IO Unit := expectUnaryCode "const r = /abc/g;" 91

-- TH0092: value-position typeof / void / delete.
def testValueTypeof : IO Unit := expectUnaryCode "const t = typeof 1;" 92
def testValueVoid : IO Unit := expectUnaryCode "const u = void 0;" 92
def testValueDelete : IO Unit :=
  expectUnaryCode "const o: { a?: number } = { a: 1 }; const r = delete o.a;" 92

-- TH0092: guard-position typeof — the regression these tests exist to prevent.
-- `===` and `!==` both go through the same rejection now (no carve-out).
def testGuardTypeofSeq : IO Unit :=
  expectUnaryCode
    "function f(x: string): number { if (typeof x === \"string\") { return 1; } return 0; }" 92
def testGuardTypeofSneq : IO Unit :=
  expectUnaryCode
    "function f(x: string): number { if (typeof x !== \"string\") { return 1; } return 0; }" 92

-- TH0092: typeof as a `switch` discriminant (also raises TH0041; `.any` is fine).
def testSwitchTypeof : IO Unit :=
  expectUnaryCode
    "function f(x: string): number { switch (typeof x) { default: return 0; } }" 92

#eval testRegexLiteral
#eval testValueTypeof
#eval testValueVoid
#eval testValueDelete
#eval testGuardTypeofSeq
#eval testGuardTypeofSneq
#eval testSwitchTypeof
