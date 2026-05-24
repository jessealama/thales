/-
  Test/TypeCheck/RefinementDiagTest.lean
  Tests the pure refinementMismatch? helper that classifies refinement-target
  mismatches into TH0080 (literal out of range) or TH0081 (needs evidence).
-/
import Thales.TypeCheck.RefinementDiag

open Thales.TypeCheck

/-- `.numberLit` against `.refinement` returns TH0080 (literalOutOfRange) with
    the target kind's name and bounds. -/
def testLiteralAgainstByte : IO Unit := do
  match refinementMismatch? (.numberLit 256.0) (.refinement .byte) "" with
  | some (.literalOutOfRange n tyName lo hi) =>
    unless n == 256.0 do throw (IO.userError s!"expected literal 256.0, got {n}")
    unless tyName == "Byte" do throw (IO.userError s!"expected 'Byte', got '{tyName}'")
    unless lo == some 0.0 && hi == some 255.0 do
      throw (IO.userError s!"expected bounds [0,255], got [{lo}, {hi}]")
  | some other => throw (IO.userError s!"expected literalOutOfRange, got {repr other}")
  | none => throw (IO.userError "expected some (.literalOutOfRange ...), got none")

/-- Plain `.number` against `.refinement` returns TH0081 (refinementNeedsEvidence)
    with the supplied sourceName folded into the message. -/
def testNumberNeedsEvidenceWithName : IO Unit := do
  match refinementMismatch? .number (.refinement .integer) "x" with
  | some (.refinementNeedsEvidence sourceName tyName) =>
    unless sourceName == "x" do throw (IO.userError s!"expected sourceName 'x', got '{sourceName}'")
    unless tyName == "Integer" do throw (IO.userError s!"expected 'Integer', got '{tyName}'")
  | some other => throw (IO.userError s!"expected refinementNeedsEvidence, got {repr other}")
  | none => throw (IO.userError "expected some, got none")

/-- Empty `sourceName` is replaced with the `"<expr>"` placeholder. -/
def testNumberNeedsEvidenceEmptyName : IO Unit := do
  match refinementMismatch? .number (.refinement .natural) "" with
  | some (.refinementNeedsEvidence sourceName _) =>
    unless sourceName == "<expr>" do
      throw (IO.userError s!"expected placeholder '<expr>', got '{sourceName}'")
  | some other => throw (IO.userError s!"expected refinementNeedsEvidence, got {repr other}")
  | none => throw (IO.userError "expected some, got none")

/-- Non-refinement target produces `none`; caller falls back to TS2322/TS2345. -/
def testNonRefinementTarget : IO Unit := do
  unless (refinementMismatch? (.numberLit 5.0) .number "").isNone do
    throw (IO.userError "expected none for non-refinement target")
  unless (refinementMismatch? .string (.refinement .byte) "").isNone do
    throw (IO.userError "expected none for non-numeric source against refinement")

/-- Refinement-to-refinement pair produces `none` — this is subtyping territory
    handled by `isSubtype`, not a TH0080/TH0081 emission case. -/
def testRefinementToRefinement : IO Unit := do
  unless (refinementMismatch? (.refinement .integer) (.refinement .byte) "").isNone do
    throw (IO.userError "expected none for refinement-to-refinement pair")

#eval testLiteralAgainstByte
#eval testNumberNeedsEvidenceWithName
#eval testNumberNeedsEvidenceEmptyName
#eval testNonRefinementTarget
#eval testRefinementToRefinement
