/-
  Test/Emit/LeanEmitModuleTest.lean
  Verifies that TS import declarations are translated to Lean import statements
  and that module output is wrapped in a namespace.
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

private def containsSubstr (h n : String) : Bool := (h.splitOn n).length ≥ 2

def expectEmit (src m : String) (needles : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog m
    for n in needles do
      unless containsSubstr out n do
        throw (IO.userError s!"missing '{n}' in:\n{out}")

def testRelativeImport : IO Unit :=
  expectEmit "import { Foo } from './geom';" "M" ["import Geom"]

def testNestedImport : IO Unit :=
  expectEmit "import { X } from './utils/arr';" "M" ["import Utils.Arr"]

def testParentImport : IO Unit :=
  expectEmit "import { Z } from '../shared/types';" "M" ["import Shared.Types"]

def testBareSpecSkip : IO Unit := do
  -- bare specifier should not appear as an import line
  match parseTSSourceNative "import { ok } from 'thales-ts';" with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog "M"
    if containsSubstr out "import Thales-ts" || containsSubstr out "import ThalesTs" then
      throw (IO.userError s!"bare specifier leaked into imports:\n{out}")

def testNamespaceWrapper : IO Unit :=
  expectEmit "interface Foo { a: boolean; }" "MyMod"
    ["namespace MyMod", "end MyMod"]

#eval testRelativeImport
#eval testNestedImport
#eval testParentImport
#eval testBareSpecSkip
#eval testNamespaceWrapper
