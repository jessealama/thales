import Thales.Parser.Native
import Thales.TypeCheck.Check
import Thales.TypeCheck.TSAST
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
      let tsDiags := typeCheck tsProg
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
        let outDir := cli.outDir.getD (dirnameOf filename)
        IO.FS.createDirAll outDir
        let outPath := outDir ++ "/" ++ moduleName ++ ".lean"
        if (← System.FilePath.pathExists outPath) && !cli.overwrite then
          IO.eprintln s!"Error: {outPath} already exists. Pass --overwrite to replace it."
          return 1
        let leanSrc := Thales.Emit.emit tsProg moduleName
        IO.FS.writeFile outPath leanSrc
        IO.eprintln s!"emitted: {outPath}"
      return 0
