import Thales.Parser.Native
import Thales.TypeCheck.Check
import Thales.TypeCheck.TSAST
import Thales.TypeCheck.ModuleExports
import Thales.TypeCheck.Diagnostic
import Thales.Emit.SubsetCheck
import Thales.Emit.DirectiveApply
import Thales.Emit.Lean

open Thales.TypeCheck
open Thales.Emit

namespace Thales.Main

structure CliArgs where
  filename : String
  emit : Bool := true
  outDir : Option String := none
  overwrite : Bool := false
  /-- Testing/harness flag: bypass `@thales-expect-error` suppression. -/
  ignoreExpectError : Bool := false
  deriving Inhabited, Repr

private def usage : String :=
  "Usage: thales [--no-emit] [--overwrite] [-o <dir>] [--ignore-expect-error] <file.ts|file.mts>"

/--
  Parse the CLI. Supports:
    * `thales file.ts`               — type-check + emit
    * `thales --no-emit file.ts`      — type-check only
    * `thales -o <dir> file.ts`       — emit into <dir>
    * `thales --overwrite file.ts`    — emit, overwriting an existing .lean
  Flags may appear in any order but must precede the filename.
-/
def parseCli (args : List String) : Except String CliArgs :=
  go args { filename := "" }
where
  go : List String → CliArgs → Except String CliArgs
    | [], _ => .error usage
    | ["--no-emit"], _ => .error usage
    | ["--overwrite"], _ => .error usage
    | ["--ignore-expect-error"], _ => .error usage
    | "-o" :: [], _ => .error usage
    | "-o" :: _ :: [], _ => .error usage
    | "--no-emit" :: rest, acc => go rest { acc with emit := false }
    | "--overwrite" :: rest, acc => go rest { acc with overwrite := true }
    | "--ignore-expect-error" :: rest, acc => go rest { acc with ignoreExpectError := true }
    | "-o" :: dir :: rest, acc => go rest { acc with outDir := some dir }
    | [file], acc =>
      if file.startsWith "-" then .error usage
      else .ok { acc with filename := file }
    | _, _ => .error usage

end Thales.Main

open Thales.Main

/-- Capitalize first letter, drop extension from basename of a path. -/
private def inputToModuleName (path : String) : String :=
  let base := path.splitOn "/" |>.getLast!
  let stem := match base.splitOn "." with
    | [s] => s
    | parts => parts.dropLast.foldl (fun acc p => acc ++ (if acc.isEmpty then "" else ".") ++ p) ""
  let stemClean := stem.toList.filter (fun c => c.isAlphanum)
  match stemClean with
  | [] => "Module"
  | c :: rest => String.ofList (c.toUpper :: rest)

private def dirnameOf (path : String) : String :=
  let parts := path.splitOn "/"
  let dirParts := parts.dropLast
  if dirParts.isEmpty then "." else String.intercalate "/" dirParts

/-- Resolve a relative module specifier against the importing file's directory.
    Returns the sibling `.ts` path, or `none` for bare/non-relative specifiers
    (e.g. `@thales/prelude`, handled inside the checker). v1 fixtures use
    same-directory `./x` specifiers. -/
private def resolveSiblingPath (importerFile : String) (spec : String) : Option String :=
  if spec.startsWith "./" then
    some (dirnameOf importerFile ++ "/" ++ spec.drop 2 ++ ".ts")
  else if spec.startsWith "../" then
    some (dirnameOf importerFile ++ "/" ++ spec ++ ".ts")  -- literal join; v1 fixtures are same-dir
  else none

/-- Recursively load the sibling-import closure of `path`, collecting each
    module's exported surface into `loaded`. `inProgress` is the chain of files
    currently being resolved; re-entering one signals an import cycle (Lean's
    module graph must be acyclic), returned as the offending `a → b → a` chain. -/
private partial def loadModule (path : String) (inProgress : List String)
    (loaded : Std.HashMap String ModuleExports) :
    IO (Std.HashMap String ModuleExports × Option String) := do
  if inProgress.contains path then
    return (loaded, some (String.intercalate " → " (inProgress ++ [path])))
  if loaded.contains path then
    return (loaded, none)
  match (← Thales.Parser.parseTSFileNative path) with
  | .error _ => return (loaded, none)   -- parse/not-found surfaces at the import site
  | .ok prog =>
    let mut ld := loaded
    let mut cyc : Option String := none
    for stmt in prog.body do
      match stmt with
      | .importDecl _ source _ .named _ =>
        match resolveSiblingPath path source with
        | some sib =>
          if (← System.FilePath.pathExists sib) then
            let (ld', c) ← loadModule sib (inProgress ++ [path]) ld
            ld := ld'
            cyc := cyc <|> c
        | none => pure ()
      | _ => pure ()
    return (ld.insert path (collectModuleExports prog), cyc)

/-- Resolve the entry module's relative sibling imports: recursively harvest each
    imported module's exported signatures (detecting cycles → TH0090), seed an
    augmented `TypeContext` (from `builtinContext`) with the harvested exports, and
    emit TS2305/TS2307 for missing members/modules. Returns the seeded context and
    the resolver diagnostics; the entry's own type check runs against the former. -/
private def resolveEntryImports (filename : String) (prog : TSProgram) :
    IO (TypeContext × Array Diagnostic) := do
  let mut ctx := builtinContext
  let mut diags : Array Diagnostic := #[]
  let mut loaded : Std.HashMap String ModuleExports := {}
  for stmt in prog.body do
    match stmt with
    | .importDecl base source specs .named _ =>
      match resolveSiblingPath filename source with
      | none => pure ()
      | some sibPath =>
        if (← System.FilePath.pathExists sibPath) then
          let (ld, cyc) ← loadModule sibPath [filename] loaded
          loaded := ld
          match cyc with
          | some chain =>
            diags := diags.push { kind := .thales (.importCycle chain), location := base.loc }
          | none => pure ()
          -- Seed even when a cycle was found: the sibling was still parsed,
          -- so binding its exports avoids a spurious TS2304 for the import.
          match ld[sibPath]? with
          | some exp =>
            -- TS2305: a named import of a member the module does not export.
            for sp in specs do
              unless exp.member? sp.imported do
                diags := diags.push
                  { kind := .noExportedMember source sp.imported, location := base.loc }
                -- Error recovery: bind the missing name as `any` (as tsc does)
                -- so its use sites don't cascade into a spurious TS2304.
                ctx := { ctx with bindings := ctx.bindings.insert sp.localName .any }
            ctx := exp.seedContext ctx specs
          | none => pure ()
        else
          -- TS2307: a relative specifier that resolves to no sibling file.
          diags := diags.push { kind := .moduleNotFound source, location := base.loc }
          for sp in specs do
            ctx := { ctx with bindings := ctx.bindings.insert sp.localName .any }
    | _ => pure ()
  return (ctx, diags)

/-- Collect names and locations of `@total`-annotated functions from a program body. -/
private def totalFuncEntries (prog : TSProgram)
    : List (String × Option Thales.AST.SourceLocation) :=
  prog.body.filterMap fun
    | .annotatedFuncDecl base name _ _ _ _ _ _ _ true => some (name, base.loc)
    | _ => none

/-- Lean termination-error substrings to look for in Lean's error output. -/
private def terminationErrorPhrases : List String :=
  [ "fail to show termination"
  , "structural recursion"
  , "could not prove termination"
  , "termination"
  ]

/-- Check whether a string looks like a Lean termination failure. -/
private def isTerminationError (s : String) : Bool :=
  terminationErrorPhrases.any (fun phrase => s.contains phrase)

/-- Run `lake env lean <path>` from `cwd` and return the output.
    Returns `none` if the process could not be spawned (e.g., `lake` not on PATH). -/
private def runLakeEnvLean (leanPath : String) (cwd : String) : IO (Option IO.Process.Output) := do
  try
    let out ← IO.Process.output {
      cmd := "lake"
      args := #["env", "lean", leanPath]
      cwd := some cwd
      stdout := .piped
      stderr := .piped
    }
    return some out
  catch _ =>
    return none

/-- Walk up from `dir` to find a directory containing `lakefile.lean` or `lakefile.toml`.
    Returns the directory path as a string, or `none` if not found within the depth limit. -/
private def findLakeRoot (dir : String) (depth : Nat) : IO (Option String) := do
  match depth with
  | 0 => return none
  | depth' + 1 =>
    let lakefileLean := dir ++ "/lakefile.lean"
    let lakefileToml := dir ++ "/lakefile.toml"
    if (← System.FilePath.pathExists lakefileLean) ||
       (← System.FilePath.pathExists lakefileToml) then
      return some dir
    -- Go up one level
    let parts := dir.splitOn "/"
    if parts.length <= 1 then return none
    let parent := String.intercalate "/" parts.dropLast
    if parent.isEmpty || parent == dir then return none
    findLakeRoot parent depth'

/-- Truncate a string to at most `n` characters for error message display. -/
private def truncateMsg (s : String) (n : Nat := 400) : String :=
  if s.length <= n then s
  else (String.ofList (s.toList.take n)) ++ "..."

/-- Check termination of `@total` functions by invoking `lake env lean` on a temp Lean file.
    Returns a list of TH0070 diagnostics (one per failing `@total` function, or a single generic one).
    Returns an empty list if the check passes or cannot be performed. -/
private def checkTotality (leanSrc : String)
    (totalEntries : List (String × Option Thales.AST.SourceLocation))
    (lakeRoot : String) : IO (Array Diagnostic) := do
  -- Write to a temp file
  let tmpDir ← IO.FS.createTempDir
  let tmpPath := tmpDir.toString ++ "/Check.lean"
  IO.FS.writeFile tmpPath leanSrc
  let resultOpt ← try
    runLakeEnvLean tmpPath lakeRoot
  finally
    try IO.FS.removeDirAll tmpDir catch _ => pure ()
  match resultOpt with
  | none => return #[]  -- could not run lake; skip check
  | some out =>
    if out.exitCode == 0 then return #[]
    -- Lean failed. Check if it's a termination error.
    let combined := out.stdout ++ out.stderr
    if !isTerminationError combined then return #[]
    let errMsg := truncateMsg combined
    -- Try to attribute to specific functions; fall back to generic
    let attributed : Array Diagnostic := totalEntries.foldl (fun acc (fname, locOpt) =>
      if combined.contains fname then
        acc.push { kind := .thales (.totalityUnverified s!"Lean reported: {errMsg}")
                   location := locOpt }
      else acc) #[]
    if !attributed.isEmpty then return attributed
    -- Generic TH0070 (no location) if we can't attribute per-function
    return #[{ kind := .thales (.totalityUnverified s!"Lean reported: {errMsg}")
               location := none }]

def main (args : List String) : IO UInt32 := do
  match parseCli args with
  | .error msg =>
    IO.eprintln msg
    return 1
  | .ok cli =>
    let filename := cli.filename
    unless filename.endsWith ".ts" || filename.endsWith ".mts" do
      IO.eprintln s!"Error: {filename} is not a TypeScript file"
      return 1
    unless (← System.FilePath.pathExists filename) do
      IO.eprintln s!"Error: File not found: {filename}"
      return 1
    match ← Thales.Parser.parseTSFileNative filename with
    | .error e =>
      IO.eprintln s!"Parse error: {e}"
      return 1
    | .ok tsProg =>
      -- Resolve relative sibling imports into an augmented type context (and
      -- TS2305/TS2307/TH0090 diagnostics) for the entry's type check.
      let (ctx, resolverDiags) ← resolveEntryImports filename tsProg
      let tsDiags := resolverDiags ++ typeCheck tsProg ctx
      let propDiags := throwsAnnotationCheck tsProg
      let throwsListDiags := throwsTypeListCheck tsProg
      let totalDiags := totalAnnotationCheck tsProg
      let rawSubsetDiags := subsetCheckIgnoringDirectives tsProg

      -- TH0070 totality check requires a Lake project to invoke `lake env lean`
      -- against. If we're outside a Lake project, the check is silently skipped.
      let totalEntries := totalFuncEntries tsProg
      let rawTotalityDiags : Array Diagnostic ← do
        if totalEntries.isEmpty || tsDiags.size > 0 then
          pure #[]
        else
          let absFilename ←
            if filename.startsWith "/" then pure filename
            else do
              let cwd ← IO.FS.realPath "."
              pure (cwd.toString ++ "/" ++ filename)
          let startDir := dirnameOf absFilename
          let lakeRootOpt ← findLakeRoot startDir 8
          match lakeRootOpt with
          | none => pure #[]
          | some lakeRoot =>
            let moduleName := inputToModuleName filename
            let leanSrc := Thales.Emit.emit tsProg moduleName
            checkTotality leanSrc totalEntries lakeRoot

      -- TH0080 (literal out of range) and TH0081 (needs evidence) are emitted
      -- by the type-checker rather than the subset-checker, because they arise
      -- during assignability checks in Check.lean. We separate them from the
      -- pure TS diagnostics and route them through DirectiveApply so that
      -- `@thales-expect-error TH0080` / `TH0081` directives can suppress them.
      let tsOnlyDiags := tsDiags.filter fun d => match d.kind with | .thales _ => false | _ => true
      let tcThDiags   := tsDiags.filter fun d => match d.kind with | .thales _ => true  | _ => false

      let allRawTh := propDiags ++ throwsListDiags ++ totalDiags ++ rawSubsetDiags ++ rawTotalityDiags ++ tcThDiags

      let thDiags : Array Diagnostic :=
        if cli.ignoreExpectError
        then allRawTh
        else DirectiveApply.apply allRawTh tsProg.expectErrorDirectives

      let allDiags : Array Diagnostic := tsOnlyDiags ++ thDiags
      let sorted := allDiags.qsort fun a b =>
        match a.location, b.location with
        | some la, some lb =>
          if la.start.line != lb.start.line then la.start.line < lb.start.line
          else la.start.column < lb.start.column
        | some _, none => true
        | none, some _ => false
        | none, none => false
      if sorted.size > 0 then
        for d in sorted do
          IO.println (d.format filename)
        return 1

      -- TH9002: a subset violation suppressed by directive can't be emitted.
      if cli.emit && DirectiveApply.hasSuppressedViolations allRawTh tsProg.expectErrorDirectives then
        let diag : Diagnostic :=
          { kind := .thales .emissionBlockedBySuppressedViolation,
            location := some { start := { line := 1, column := 0 },
                               «end» := { line := 1, column := 0 } } }
        IO.println (diag.format filename)
        return 1

      if cli.emit then
        let moduleName := inputToModuleName filename
        -- TH9005: structural emit-soundness gate. Build the module once; if it
        -- contains any LExpr.unsupported placeholder, refuse to write a file that
        -- cannot elaborate. Non-suppressible — this is an internal integrity check.
        let mod := Thales.Emit.buildModule tsProg moduleName
        let unsupported := mod.unsupportedReasons
        if !unsupported.isEmpty then
          let diag : Diagnostic :=
            { kind := .thales (.emittedCodeContainsUnsupported (String.intercalate "; " unsupported)),
              location := some { start := { line := 1, column := 0 },
                                 «end» := { line := 1, column := 0 } } }
          IO.println (diag.format filename)
          return 1
        let outDir := cli.outDir.getD (dirnameOf filename)
        IO.FS.createDirAll outDir
        let outPath := outDir ++ "/" ++ moduleName ++ ".lean"
        if (← System.FilePath.pathExists outPath) && !cli.overwrite then
          IO.eprintln s!"Error: {outPath} already exists. Pass --overwrite to replace it."
          return 1
        let leanSrc := Thales.Emit.LeanSyntax.renderModule mod
        IO.FS.writeFile outPath leanSrc
        IO.eprintln s!"emitted: {outPath}"
      return 0
