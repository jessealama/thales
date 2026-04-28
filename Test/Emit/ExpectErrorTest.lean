import Thales.Emit.DirectiveApply
import Thales.TypeCheck.Diagnostic

namespace Thales.Emit.DirectiveApply.Test
open Thales.TypeCheck Thales.Parser

private def mkLoc (line col : Nat) : Thales.AST.SourceLocation :=
  { start := { line, column := col }, «end» := { line, column := col } }

private def thDiag (kind : ThalesKind) (line : Nat) : Diagnostic :=
  { kind := .thales kind, location := some (mkLoc line 0) }

private def dirAt (dLine aLine : Nat) (code : Option Nat) (mal : Bool := false)
    : ExpectErrorDirective :=
  { directiveLine := dLine, appliesToLine := aLine, expectedCode := code, malformed := mal }

-- Match ⇒ all TH on applied line suppressed.
#guard
  let raw := #[thDiag (.cannotReassignVariable "x") 2]
  let dirs := #[dirAt 1 2 (some 1)]
  (apply raw dirs).size = 0

-- Wrong code ⇒ TH9001 at directive line, originals kept.
#guard
  let raw := #[thDiag (.cannotReassignVariable "x") 2]
  let dirs := #[dirAt 1 2 (some 2)]
  let out := apply raw dirs
  out.size = 2 &&
  out.any (fun d => match d.kind with
    | .thales (.directiveCodeMismatch 2 [1]) => true
    | _ => false) &&
  out.any (fun d => match d.kind with
    | .thales (.cannotReassignVariable _) => true
    | _ => false)

-- No TH at applied line ⇒ TH9000.
#guard
  let dirs := #[dirAt 1 2 (some 1)]
  let out := apply #[] dirs
  out.size = 1 &&
  out.any (fun d => match d.kind with
    | .thales .directiveUnused => true
    | _ => false)

-- Code-less matches any TH and suppresses all.
#guard
  let raw := #[thDiag (.cannotReassignVariable "x") 2, thDiag .cannotAssignArrayElement 2]
  let dirs := #[dirAt 1 2 none]
  (apply raw dirs).size = 0

-- Multi-code line: declared code is among the codes ⇒ all suppressed.
#guard
  let raw := #[thDiag .classNotSupported 3, thDiag .inheritanceNotSupported 3]
  let dirs := #[dirAt 2 3 (some 31)]
  (apply raw dirs).size = 0

-- Malformed ⇒ TH9003, no suppression.
#guard
  let raw := #[thDiag (.cannotReassignVariable "x") 2]
  let dirs := #[dirAt 1 2 none true]
  let out := apply raw dirs
  out.size = 2 &&
  out.any (fun d => match d.kind with
    | .thales .directiveMalformed => true
    | _ => false)

-- EOF directive (appliesToLine = 0) ⇒ always TH9000.
#guard
  let dirs := #[dirAt 1 0 (some 1)]
  let out := apply #[] dirs
  out.any (fun d => match d.kind with
    | .thales .directiveUnused => true
    | _ => false)

end Thales.Emit.DirectiveApply.Test
