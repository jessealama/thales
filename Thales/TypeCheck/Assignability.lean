/-
  Thales/TypeCheck/Assignability.lean
  Assignment-side gate: `checkAssignable` runs the subtype check and emits
  either a refinement-target mismatch (TH0080 / TH0081, classified by
  `refinementMismatch?`) or the generic TS2322 fallback.

  Lives outside `Generic.lean` because it sits *above* the mutual cycle —
  it only consumes `isSubtype` and `resolveTypeGeneric`, never feeds back
  into them.
-/
import Thales.TypeCheck.TSType
import Thales.TypeCheck.Context
import Thales.TypeCheck.Diagnostic
import Thales.TypeCheck.RefinementDiag
import Thales.TypeCheck.Generic

set_option autoImplicit false

namespace Thales.TypeCheck

open Thales.AST

/-- Check assignability and emit a diagnostic if it fails.
    Refinement-target mismatches are classified by `refinementMismatch?` and
    surface as TH0080 / TH0081; everything else falls back to TS2322. -/
def checkAssignable (source target : TSType) (loc : Option SourceLocation := none)
    (sourceName : String := "") : TypeCheckM Unit := do
  let ok ← isSubtype source target
  if !ok then
    let resolvedSource ← resolveTypeGeneric source
    let resolvedTarget ← resolveTypeGeneric target
    match refinementMismatch? resolvedSource resolvedTarget sourceName with
    | some thKind => emitDiagnostic (.thales thKind) loc
    | none => emitDiagnostic (.typeNotAssignable source target) loc

end Thales.TypeCheck
