/-
  Test/Emit/ClassEmitTest.lean
  Class lowering (#106): a v1 class emits `structure C where <fields>` plus
  `namespace C` holding `def ctor'` and receiver-first `partial def`s;
  `new C(args)` lowers to `C.ctor' args`; method calls resolve via Lean
  generalized field notation; namespace names escape Lean keywords; the
  private-marking pass distributes into class namespaces.
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

def expectNoEmit (src moduleName : String) (needles : List String) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let out := emit prog moduleName
    for n in needles do
      if containsSubstr out n then
        throw (IO.userError s!"unexpected '{n}' in:\n{out}")

private def pointSrc : String :=
  "class Point {\n" ++
  "  readonly x: bigint;\n" ++
  "  readonly y: bigint;\n" ++
  "  constructor(x: bigint, y: bigint) { this.x = x; this.y = y; }\n" ++
  "  norm1(): bigint { return this.x < 0n ? -this.x : this.x; }\n" ++
  "  translate(dx: bigint, dy: bigint): Point { return new Point(this.x + dx, this.y + dy); }\n" ++
  "}\n" ++
  "const p = new Point(3n, -4n);\n" ++
  "console.log(p.norm1());\n"

-- The full lowering shape for the Point class
def testPointLowering : IO Unit :=
  expectEmit pointSrc "M"
    [ "structure Point where",
      "x : Int",
      "y : Int",
      "deriving Repr, BEq",
      "namespace Point",
      "def ctor' (x : Int) (y : Int) : Point :=",
      "let x := x",
      "let y := y",
      "x := x, y := y : Point",
      "partial def norm1 (self' : Point) : Int",
      "self'.x",
      "partial def translate (self' : Point) (dx : Int) (dy : Int) : Point",
      "end Point",
      "Point.ctor' 3 ((Neg.neg 4))",
      "p.norm1" ]

#eval testPointLowering

-- Namespace escaping: a class named by a Lean keyword (`theorem` is a legal
-- TS identifier) gets guillemets in namespace/end lines and ctor references
def testKeywordClassName : IO Unit :=
  expectEmit
    ("class theorem {\n" ++
     "  readonly v: bigint;\n" ++
     "  constructor(v: bigint) { this.v = v; }\n" ++
     "}\n" ++
     "const t = new theorem(1n);\n" ++
     "console.log(t.v);\n") "M"
    [ "structure «theorem» where",
      "namespace «theorem»",
      "end «theorem»",
      "«theorem».ctor' 1" ]

#eval testKeywordClassName

-- Export marking: exported class stays public; a non-exported class in an
-- exporting module distributes privacy into its namespace (there is no legal
-- `private namespace`)
def testExportPrivacyDistribution : IO Unit := do
  let src :=
    "export class Point {\n" ++
    "  readonly x: bigint;\n" ++
    "  constructor(x: bigint) { this.x = x; }\n" ++
    "  get1(): bigint { return this.x; }\n" ++
    "}\n" ++
    "class Hidden {\n" ++
    "  readonly y: bigint;\n" ++
    "  constructor(y: bigint) { this.y = y; }\n" ++
    "  get2(): bigint { return this.y; }\n" ++
    "}\n"
  expectEmit src "Geom"
    [ "structure Point where",
      "private structure Hidden where",
      "private def ctor'",
      "private partial def get2" ]
  expectNoEmit src "Geom"
    [ "private structure Point where",
      "private namespace",
      "private partial def get1" ]

#eval testExportPrivacyDistribution

-- Structural construction for free: class fields register in structFields,
-- so an annotated object literal against the class type emits a struct
-- literal (tsc-legal only for a method-less class)
def testStructuralConstruction : IO Unit :=
  expectEmit
    ("class Pair {\n" ++
     "  readonly x: bigint;\n" ++
     "  readonly y: bigint;\n" ++
     "  constructor(x: bigint, y: bigint) { this.x = x; this.y = y; }\n" ++
     "}\n" ++
     "const q: Pair = { x: 1n, y: 2n };\nconsole.log(q.x);\n") "M"
    [ "x := 1, y := 2 : Pair" ]

#eval testStructuralConstruction

#eval IO.println "ClassEmitTest: OK"
