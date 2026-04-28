/-
  Thales/Emit/DirectiveApply.lean
  Post-process raw subset-check diagnostics against collected
  `@thales-expect-error` directives.
-/
import Thales.TypeCheck.Diagnostic
import Thales.Parser.ExpectError
import Std.Data.HashMap
import Std.Data.HashSet

namespace Thales.Emit.DirectiveApply

open Thales.TypeCheck Thales.Parser

/-- Source line of a diagnostic, or 0 if it lacks a location. -/
private def diagLine (d : Diagnostic) : Nat :=
  match d.location with
  | some loc => loc.start.line
  | none => 0

/-- Emit a synthesised directive-diagnostic at `line`. -/
private def dirDiag (kind : ThalesKind) (line : Nat) : Diagnostic :=
  { kind := .thales kind,
    location := some { start := { line, column := 0 }, «end» := { line, column := 0 } } }

/-- True if the diagnostic is a TH (Thales subset) kind. -/
private def isThalesDiag (d : Diagnostic) : Bool :=
  match d.kind with
  | .thales _ => true
  | _ => false

/-- Apply directive-based suppression/validation to `raw` diagnostics.
    Returns the final diagnostic set visible to the user (under default
    behavior — `--ignore-expect-error` bypasses this and returns `raw`). -/
def apply (raw : Array Diagnostic) (dirs : Array ExpectErrorDirective)
    : Array Diagnostic := Id.run do
  -- Separate TH diagnostics (eligible for suppression) from TS diagnostics.
  let th := raw.filter isThalesDiag
  let ts := raw.filter (fun d => !isThalesDiag d)
  -- Group TH codes by line.
  let mut byLine : Std.HashMap Nat (Array Diagnostic) := {}
  for d in th do
    let ln := diagLine d
    byLine := byLine.insert ln ((byLine.getD ln #[]).push d)
  -- Track lines that have been suppressed.
  let mut suppressedLines : Std.HashSet Nat := {}
  -- Collect synthesised diagnostics from directives.
  let mut synth : Array Diagnostic := #[]
  for dir in dirs do
    if dir.malformed then
      synth := synth.push (dirDiag .directiveMalformed dir.directiveLine)
      continue
    let appliedLine := dir.appliesToLine
    let group := byLine.getD appliedLine #[]
    if appliedLine == 0 || group.isEmpty then
      synth := synth.push (dirDiag .directiveUnused dir.directiveLine)
      continue
    -- Codes actually fired on the applied line.
    let actualCodes : List Nat := group.toList.filterMap fun d =>
      match d.kind with | .thales t => some t.thCode | _ => none
    match dir.expectedCode with
    | none =>
      -- Code-less directive: match any TH; suppress the whole group.
      suppressedLines := suppressedLines.insert appliedLine
    | some expected =>
      if actualCodes.contains expected then
        suppressedLines := suppressedLines.insert appliedLine
      else
        synth := synth.push
          (dirDiag (.directiveCodeMismatch expected actualCodes) dir.directiveLine)
  -- Build the final output: TS diagnostics always, TH diagnostics only if
  -- their line wasn't suppressed, plus synthesised directive diagnostics.
  let keptTh := th.filter fun d => !suppressedLines.contains (diagLine d)
  return ts ++ keptTh ++ synth

/-- True if any raw TH diagnostic's line was suppressed by a directive.
    Used by the emit-mode gate to decide whether to emit TH9002. -/
def hasSuppressedViolations (raw : Array Diagnostic) (dirs : Array ExpectErrorDirective)
    : Bool := Id.run do
  let th := raw.filter isThalesDiag
  let mut byLine : Std.HashMap Nat (Array Diagnostic) := {}
  for d in th do
    byLine := byLine.insert (diagLine d) ((byLine.getD (diagLine d) #[]).push d)
  for dir in dirs do
    if dir.malformed then continue
    let group := byLine.getD dir.appliesToLine #[]
    if dir.appliesToLine == 0 || group.isEmpty then continue
    let actualCodes : List Nat := group.toList.filterMap fun d =>
      match d.kind with | .thales t => some t.thCode | _ => none
    match dir.expectedCode with
    | none => return true
    | some expected => if actualCodes.contains expected then return true
  return false

end Thales.Emit.DirectiveApply
