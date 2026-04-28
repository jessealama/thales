/-
  Test/Emit/LeanEmitTypesTest.lean
  Verifies that the Lean emitter produces correct output for primitive type
  aliases, generic aliases, and interface declarations.
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

/-- Return true if `needle` appears as a substring of `hay`. -/
private def containsSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length ≥ 2

/-- Run `emit` on `src` and verify each needle appears in the output. -/
def expectEmit (src : String) (moduleName : String) (needles : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog moduleName
    for n in needles do
      unless containsSubstr out n do
        throw (IO.userError s!"missing '{n}' in:\n{out}")

def testPrimitiveAlias : IO Unit :=
  expectEmit "type N = number;" "M" ["abbrev N := Float"]

def testBigintAlias : IO Unit :=
  expectEmit "type I = bigint;" "M" ["abbrev I := Int"]

def testStringAlias : IO Unit :=
  expectEmit "type S = string;" "M" ["abbrev S := String"]

def testGenericAlias : IO Unit :=
  -- renderTypeParams uses implicit binders: {T : Type}
  expectEmit "type Box<T> = T[];" "M" ["abbrev Box", "{T : Type}", "Array T"]

def testRecord : IO Unit :=
  expectEmit "interface Point { x: number; y: number; }" "M"
    ["structure Point where", "x : Float", "y : Float"]

def testNamespace : IO Unit :=
  expectEmit "interface Foo { a: boolean; }" "MyMod"
    ["namespace MyMod", "end MyMod"]

def testImports : IO Unit :=
  expectEmit "interface A { x: number; }" "M"
    ["import Thales.TS.Runtime", "open Thales.TS"]

#eval testPrimitiveAlias
#eval testBigintAlias
#eval testStringAlias
#eval testGenericAlias
#eval testRecord
#eval testNamespace
#eval testImports
