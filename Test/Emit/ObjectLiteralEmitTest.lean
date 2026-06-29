/-
  Test/Emit/ObjectLiteralEmitTest.lean
  Object-literal construction (#15/#81) and single-record type aliases (#13).
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser

private def containsSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length ≥ 2

def expectEmit (src moduleName : String) (needles : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog moduleName
    for n in needles do
      unless containsSubstr out n do
        throw (IO.userError s!"missing '{n}' in:\n{out}")

-- #13: a single-record `type` alias must emit `structure`, not `abbrev … := Unit`.
def testTypeAliasRecordStruct : IO Unit :=
  expectEmit
    "type PortRange = { start: bigint; endPort: bigint };
     function lo(r: PortRange): bigint { return r.start; }" "M"
    ["structure PortRange where", "start : Int", "endPort : Int"]

#eval testTypeAliasRecordStruct
