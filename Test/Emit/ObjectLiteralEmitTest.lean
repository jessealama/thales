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

-- #15/#81: constructing an interface value via `{ x, y }` in return position.
def testInterfaceReturnConstruct : IO Unit :=
  expectEmit
    "interface Pair { x: bigint; y: bigint }
     function mk(x: bigint, y: bigint): Pair { return { x, y }; }" "M"
    ["x := x", "y := y", ": Pair"]

-- #15/#81: same for a single-record type alias, explicit-key form.
def testTypeAliasReturnConstruct : IO Unit :=
  expectEmit
    "type Pair = { x: bigint; y: bigint };
     function mk(x: bigint, y: bigint): Pair { return { x: x, y: y }; }" "M"
    ["x := x", "y := y", ": Pair"]

#eval testInterfaceReturnConstruct
#eval testTypeAliasReturnConstruct

-- Annotated local: `const p: Pair = { x, y };`
def testAnnotatedLocalConstruct : IO Unit :=
  expectEmit
    "interface Pair { x: bigint; y: bigint }
     function f(x: bigint, y: bigint): bigint { const p: Pair = { x, y }; return p.x; }" "M"
    ["let p", "x := x", "y := y", ": Pair"]

#eval testAnnotatedLocalConstruct

-- Nested record: a field whose value is itself an object literal.
def testNestedConstruct : IO Unit :=
  expectEmit
    "interface Inner { v: bigint }
     interface Outer { inner: Inner; tag: bigint }
     function mk(v: bigint): Outer { return { inner: { v: v }, tag: 0n }; }" "M"
    ["v := v", ": Inner", "tag :=", ": Outer"]

#eval testNestedConstruct

-- Call argument: `consume({ x, y })` where the param type is a known struct.
def testCallArgConstruct : IO Unit :=
  expectEmit
    "interface Pair { x: bigint; y: bigint }
     function consume(p: Pair): bigint { return p.x; }
     function go(x: bigint, y: bigint): bigint { return consume({ x, y }); }" "M"
    ["x := x", "y := y", ": Pair"]

-- Array of records: `const xs: Pair[] = [{ x: 1n, y: 2n }];`
def testArrayOfRecords : IO Unit :=
  expectEmit
    "interface Pair { x: bigint; y: bigint }
     function f(): bigint { const xs: Pair[] = [{ x: 1n, y: 2n }]; return 0n; }" "M"
    ["x :=", "y :=", ": Pair", "List.toArray"]

#eval testCallArgConstruct
#eval testArrayOfRecords

-- Existing DU construction must still lower to a constructor application.
def testDUStillCtor : IO Unit :=
  expectEmit
    "type Shape = { kind: 'circle'; r: bigint } | { kind: 'square'; s: bigint };
     function mk(r: bigint): Shape { return { kind: 'circle', r }; }" "M"
    [".circle"]

-- A struct with a field literally named `kind` is built as a struct, not
-- mis-lowered to a constructor, because the target is a known structure.
def testStructWithKindField : IO Unit :=
  expectEmit
    "interface Tagged { kind: bigint; v: bigint }
     function mk(k: bigint, v: bigint): Tagged { return { kind: k, v }; }" "M"
    ["kind := k", "v := v", ": Tagged"]

#eval testDUStillCtor
#eval testStructWithKindField

-- An anonymous-object return type has no named Lean structure to construct, so
-- the object literal stays `.unsupported` and the non-suppressible TH9005
-- emit-gate (Main) blocks emission. (Can't be a `reject/` fixture: TH9005 is an
-- emit-phase gate that does not fire under `--no-emit`, which the harness uses.)
def testAnonObjectReturnUnsupported : IO Unit :=
  expectEmit
    "function f(): { x: bigint } { return { x: 1n }; }" "M"
    ["(unsupported:"]

#eval testAnonObjectReturnUnsupported

-- A record TYPE name that is a Lean keyword (legal TS identifier) must be
-- escaped at emit — in the `structure` declaration, the return-type ascription,
-- and the `{ … : T }` construction — or the emitted Lean fails to compile.
def testKeywordTypeNameEscaped : IO Unit :=
  expectEmit
    "interface end { v: bigint }
     function mk(v: bigint): end { return { v }; }" "M"
    ["structure «end» where", ": «end» :=", "v := v : «end»"]

#eval testKeywordTypeNameEscaped
