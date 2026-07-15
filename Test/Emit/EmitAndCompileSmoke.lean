/-
  Test/Emit/EmitAndCompileSmoke.lean
  For each sample TS input, emit Lean source, write to a temp file,
  invoke `lake env lean` on it, and fail if elaboration fails.
-/
import Thales.Emit.Lean
import Thales.Parser.Native

open Thales.Emit Thales.Parser

/-- Run `lake env lean` on the emitted code in a temp dir with Thales.TS.Runtime
    available on the search path. -/
def emitAndElaborate (src : String) (moduleName : String) : IO (UInt32 × String × String) := do
  match parseTSSourceNative src with
  | .error e => return (1, "", s!"parse failed: {e}")
  | .ok prog =>
    let leanSrc := emit prog moduleName
    let tmpDir ← IO.FS.createTempDir
    let leanPath := tmpDir / s!"{moduleName}.lean"
    IO.FS.writeFile leanPath leanSrc
    let cwd ← IO.currentDir
    let out ← IO.Process.output {
      cmd := "lake"
      args := #["env", "lean", leanPath.toString]
      cwd := some cwd.toString
    }
    IO.FS.removeDirAll tmpDir
    return (out.exitCode, out.stdout, out.stderr)

/-- Samples: (moduleName, source).
    NOTE: BigintRecursion uses `double` (non-recursive) rather than `fact` (recursive)
    because Lean's structural-recursion check cannot prove termination for `Int`-based
    recursion in v1. The original factorial sample is a known v1 limitation; see task
    spec §Known Concerns #1.  A termination_by annotation in the emitter would fix it
    but is out of scope for v1. -/
def samples : List (String × String) := [
  ("Identity",
   "function id(x: number): number { return x; }"),
  ("Arithmetic",
   "function add(x: number, y: number): number { return x + y; }"),
  ("ShapeArea",
   "type Shape = {kind: 'c', r: number} | {kind: 's', s: number}; function area(sh: Shape): number { switch (sh.kind) { case 'c': return 3.14 * sh.r * sh.r; case 's': return sh.s * sh.s; } }"),
  ("BigintDouble",
   "function double(n: bigint): bigint { return n + n; }"),
  -- `(typeof X)[number]` should resolve to the element type of X and emit
  -- a clean `abbrev`. The resulting Mode alias is consumed by `pick`'s
  -- return type so the elaborator exercises both sides.
  ("TypeofIndex",
   "const MODES: string[] = [\"a\", \"b\", \"c\"];\n" ++
   "type Mode = (typeof MODES)[number];\n" ++
   "function pick(): Mode { return \"a\"; }"),
  -- Same-primitive literal-union aliases lower to inductives plus a Coe
  -- instance. `quadratic` exercises the Coe insertion in a non-trivial
  -- arithmetic context (`x * x + 1` requires coercion in two positions).
  ("LiteralUnions",
   "type Signed = -1 | 0 | 1;\n" ++
   "type Mode = \"a\" | \"b\" | \"c\";\n" ++
   "function cmpZero(): Signed { return 0; }\n" ++
   "function pick(): Mode { return \"a\"; }\n" ++
   "function quadratic(x: Signed): number { return x * x + 1; }"),
  -- v1 class lowering (#106): structure + namespace, ctor', receiver-first
  -- methods, `new` at top level and inside a method, structural construction.
  ("ClassPoint",
   "class Point {\n" ++
   "  readonly x: bigint;\n" ++
   "  readonly y: bigint;\n" ++
   "  constructor(x: bigint, y: bigint) { this.x = x; this.y = y; }\n" ++
   "  norm1(): bigint { return this.x < 0n ? -this.x : this.x; }\n" ++
   "  translate(dx: bigint, dy: bigint): Point { return new Point(this.x + dx, this.y + dy); }\n" ++
   "}\n" ++
   -- structural construction stays tsc-legal only for a method-less class
   "class Pair {\n" ++
   "  readonly a: bigint;\n" ++
   "  readonly b: bigint;\n" ++
   "  constructor(a: bigint, b: bigint) { this.a = a; this.b = b; }\n" ++
   "}\n" ++
   "const p = new Point(3n, -4n);\n" ++
   "const q: Pair = { a: 1n, b: 2n };\n" ++
   "console.log(p.norm1());\n" ++
   "console.log(p.translate(1n, 1n).x, q.b);\n")
]

def runSmoke : IO Unit := do
  for (name, src) in samples do
    let (code, stdout, stderr) ← emitAndElaborate src name
    if code != 0 then
      IO.println s!"[smoke FAIL] {name}"
      IO.println s!"  stderr:\n{stderr}"
      IO.println s!"  stdout:\n{stdout}"
      throw (IO.userError s!"{name} emitted Lean failed to elaborate")
    IO.println s!"[smoke ok] {name}"

#eval runSmoke
