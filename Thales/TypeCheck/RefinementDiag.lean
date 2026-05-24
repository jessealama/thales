/-
  Thales/TypeCheck/RefinementDiag.lean
  Classifies a (source, target) type pair as a refinement-target mismatch
  and returns the corresponding TH0080/TH0081 diagnostic kind.

  This is a pure helper. Callers (`Generic.checkAssignable`,
  `Synth.emitArgMismatch`) resolve type aliases via `resolveTypeGeneric`
  before calling, and fall back to their own TS#### diagnostic when this
  returns `none`.
-/
import Thales.TypeCheck.TSType
import Thales.TypeCheck.Diagnostic

set_option autoImplicit false

namespace Thales.TypeCheck

/-- Classify a `(resolvedSrc, resolvedTgt)` pair as a refinement-target mismatch.

    Returns:
      - `some (.literalOutOfRange …)` (TH0080) when source is a `.numberLit`
        outside the target refinement's range.
      - `some (.refinementNeedsEvidence …)` (TH0081) when source is plain
        `number` against a refinement target.
      - `none` for any other pair — the caller emits its own fallback
        (TS2322 from `checkAssignable`, TS2345 from `emitArgMismatch`, etc.).

    `sourceName` is folded into TH0081's message ("Value '<name>'…"); pass
    `""` if the source isn't a simple identifier and the default `"<expr>"`
    placeholder should be used. -/
def refinementMismatch?
    (resolvedSrc resolvedTgt : TSType) (sourceName : String := "")
    : Option ThalesKind :=
  match resolvedSrc, resolvedTgt with
  | .numberLit n, .refinement k =>
    let (lo, hi) := k.bounds
    some (.literalOutOfRange n k.name lo hi)
  | .number, .refinement k =>
    let nm := if sourceName.isEmpty then "<expr>" else sourceName
    some (.refinementNeedsEvidence nm k.name)
  | _, _ => none

end Thales.TypeCheck
