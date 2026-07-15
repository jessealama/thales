/-
  Test/TypeCheck/ClassTypingTest.lean
  Real class typing (#106): instance types built from retained annotations,
  ctor signatures (TS2554/TS2345 on `new`), `this` typing inside members,
  readonly flowing into AssignTarget (TS2540), and the class surface of
  module export/import.
-/
import Thales.TypeCheck.Check
import Thales.TypeCheck.ModuleExports
import Thales.TypeCheck.Builtins
import Thales.Parser.Native

open Thales.TypeCheck
open Thales.Parser

private def parseOrThrow (src : String) : IO TSProgram := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog => return prog

private def diagsOf (src : String) (ctx : TypeContext := builtinContext) : IO (Array Diagnostic) := do
  let prog ← parseOrThrow src
  return typeCheck prog ctx

private def hasTS (d : Diagnostic) (code : Nat) : Bool :=
  ((d.format "t.ts").splitOn s!"error TS{code}:").length > 1

def expectTS (src : String) (code : Nat) (ctx : TypeContext := builtinContext) : IO Unit := do
  let diags ← diagsOf src ctx
  unless diags.any (hasTS · code) do
    let formatted := (diags.map (·.format "t.ts")).toList
    throw (IO.userError s!"expected TS{code}, got: {formatted}")

def expectNoDiags (src : String) (ctx : TypeContext := builtinContext) : IO Unit := do
  let diags ← diagsOf src ctx
  unless diags.isEmpty do
    let formatted := (diags.map (·.format "t.ts")).toList
    throw (IO.userError s!"expected no diagnostics, got: {formatted}")

private def pointClass : String :=
  "class Point {\n" ++
  "  readonly x: bigint;\n" ++
  "  readonly y: bigint;\n" ++
  "  constructor(x: bigint, y: bigint) { this.x = x; this.y = y; }\n" ++
  "  norm1(): bigint { return this.x < 0n ? -this.x : this.x; }\n" ++
  "  translate(dx: bigint, dy: bigint): Point { return new Point(this.x + dx, this.y + dy); }\n" ++
  "}\n"

-- 1. Supported shape: construction and method calls are clean (the spurious
--    TS2554 on method calls observed with the all-`any` model must be gone).
def t1 : IO Unit := expectNoDiags
  (pointClass ++ "const p = new Point(3n, -4n);\nconst n = p.norm1();\nconst q = p.translate(1n, 1n);\n")

-- 2. Ctor arity: TS2554
def t2 : IO Unit := expectTS (pointClass ++ "const p = new Point(1n);\n") 2554

-- 3. Ctor arg type: TS2345
def t3 : IO Unit := expectTS (pointClass ++ "const p = new Point(1n, \"x\");\n") 2345

-- 4. Unknown member: TS2339
def t4 : IO Unit := expectTS (pointClass ++ "const p = new Point(1n, 2n);\nconst z = p.nope();\n") 2339

-- 5. Readonly field assignment: TS2540
def t5 : IO Unit := expectTS (pointClass ++ "const p = new Point(1n, 2n);\np.x = 5n;\n") 2540

-- 6. `this` is instance-typed inside methods: `this.nope` is TS2339
def t6 : IO Unit := expectTS
  ("class C {\n" ++
   "  readonly x: bigint;\n" ++
   "  constructor(x: bigint) { this.x = x; }\n" ++
   "  bad(): bigint { return this.nope; }\n" ++
   "}\n") 2339

-- 7. Module surface: export class → ModuleExports.classes; import seeds the
--    importer's context so `new`, arity, and readonly all work across files.
private def geomSrc : String :=
  "export " ++ pointClass

private def importHeader : String :=
  "import { Point } from \"./geom\";\n"

def exportSurface : IO (ModuleExports × TypeContext) := do
  let depProg ← parseOrThrow geomSrc
  let exp := collectModuleExports depProg
  let spec : ModuleSpecifier := { imported := "Point", localName := "Point" }
  let ctx := exp.seedContext builtinContext [spec]
  return (exp, ctx)

def t7a : IO Unit := do
  let (exp, _) ← exportSurface
  match exp.classes.find? (·.1 == "Point") with
  | some (_, info) =>
    match info.ctorParams with
    | [(n1, TSType.bigint), (n2, TSType.bigint)] =>
      unless n1 == "x" && n2 == "y" do
        throw (IO.userError s!"ctorParams names: {n1}, {n2}")
    | _ => throw (IO.userError s!"ctorParams shape wrong ({info.ctorParams.length} params)")
  | none => throw (IO.userError "Point not in ModuleExports.classes")

def t7b : IO Unit := do
  let (_, ctx) ← exportSurface
  expectNoDiags (importHeader ++ "const p = new Point(3n, -4n);\nconst q = p.translate(1n, 1n);\n") ctx

def t7c : IO Unit := do
  let (_, ctx) ← exportSurface
  expectTS (importHeader ++ "const p = new Point(1n);\n") 2554 ctx

def t7d : IO Unit := do
  let (_, ctx) ← exportSurface
  expectTS (importHeader ++ "const p = new Point(1n, 2n);\np.x = 5n;\n") 2540 ctx

#eval t1
#eval t2
#eval t3
#eval t4
#eval t5
#eval t6
#eval t7a
#eval t7b
#eval t7c
#eval t7d
#eval IO.println "ClassTypingTest: OK"
