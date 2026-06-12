/-
  Test/TypeCheck/IndexAccessTest.lean
  Pins computed element access: `xs[i]` on arrays synthesizes
  `T | undefined` (the noUncheckedIndexedAccess mirror); arithmetic on the
  un-narrowed result draws TH0082; computed access on non-arrays draws
  TH0083. tsc accepts every program here — TH0082/83 are subset
  boundaries, not tsc mirrors.
-/
import Thales.TypeCheck.Check
import Thales.Parser.Native

open Thales.TypeCheck
open Thales.Parser

private def diagsOf (src : String) : IO (Array Diagnostic) := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog => return typeCheck prog

private def expectTH (code : Nat) (src : String) : IO Unit := do
  let diags ← diagsOf src
  unless diags.any (·.thalesCode? == some code) do
    let formatted := (diags.map (·.format "t.ts")).toList
    throw (IO.userError s!"expected TH{code}, got: {formatted}")

private def expectClean (src : String) : IO Unit := do
  let diags ← diagsOf src
  unless diags.isEmpty do
    let formatted := (diags.map (·.format "t.ts")).toList
    throw (IO.userError s!"expected no diagnostics, got: {formatted}")

-- Narrowed element read: synthesizes string | undefined, narrows to string.
def t_narrowedRead : IO Unit := expectClean
  "const xs: string[] = [\"a\"];
function f(i: number): string { const hit = xs[i]; if (hit !== undefined) { return hit; } return \"\"; }"

-- xs[i] is T | undefined: assigning it where T is required is TS2322.
def t_uncheckedAssign : IO Unit := do
  let diags ← diagsOf
    "const xs: string[] = [\"a\"];
const y: string = xs[0];"
  unless diags.any (·.kind.tscCode == 2322) do
    let formatted := (diags.map (·.format "t.ts")).toList
    throw (IO.userError s!"expected TS2322, got: {formatted}")

-- Un-narrowed arithmetic on the option result draws TH0082.
def t_optionPlus : IO Unit := expectTH 82
  "const xs: string[] = [\"a\"];
function f(i: number): string { return xs[i] + \"!\"; }"

-- Relational comparison on an option operand draws TH0082 too.
def t_optionLt : IO Unit := expectTH 82
  "const xs: number[] = [1];
function f(i: number): boolean { return xs[i] < 3; }"

-- Equality tests against undefined stay clean (the narrowing primitive).
def t_eqUndefinedClean : IO Unit := expectClean
  "const xs: string[] = [\"a\"];
function f(i: number): boolean { return xs[i] !== undefined; }"

-- Computed access on a non-array draws TH0083.
def t_stringIndex : IO Unit := expectTH 83
  "function f(s: string): string | undefined { return s[0]; }"

#eval t_narrowedRead
#eval t_uncheckedAssign
#eval t_optionPlus
#eval t_optionLt
#eval t_eqUndefinedClean
#eval t_stringIndex
