# Thales

Thales is a TypeScript-to-Lean 4 compiler that accepts a strict subset of `tsc --strict` and emits a Lean 4 sidecar mirroring the program's runtime behavior. The user-visible artifact is the `thales` CLI; the compiler's correctness is defined operationally by the conformance harness.

## Language

### Refinement-types vocabulary

**Prelude library types**:
The four numerical types Thales ships out-of-the-box in `@thales/prelude`: `Integer` (safe integer), `Natural` (non-negative safe integer), `Byte` (`0..255`), `Bit` (`0` or `1`). On the TS side these are bare aliases of `number`; on the Lean side they are `Subtype { x : Float // p x = true }`. Lattice: `Bit ⊂ Byte ⊂ Natural ⊂ Integer ⊂ number`. **Internal codebase term;** user-facing copy (README, release notes) calls these "built-in bounded number types" or names them concretely (`Integer`, `Natural`, `Byte`, `Bit`) — "prelude" has no antecedent for a user encountering Thales fresh.
_Avoid_: "refinement types" (ambiguous — see Flagged ambiguities)

**Provably-safe array indexing**:
The user-facing feature that lifts `arr[i] : T | undefined` to `arr[i] : T` when Thales can prove the index is in bounds. Covers two patterns: P1 (literal index into literal/tuple array) and P2 (length-narrowed access with a `Natural`-typed index). Stretch goal P3 (iteration callbacks) deferred. **Deferred** — split out of v0.6 to keep that release small and reviewable, then re-sequenced past v0.7 (which became a 0.6-completeness release); see ADR-0001 and ADR-0002.
_Avoid_: "indexing refinements", "bounds checking"

**Subtype machinery**:
The Lean-side scaffolding that gives the prelude library types proof-bearing representations: Subtype definitions, `Coe` instances for the lattice chain, the three homomorphism boundary axioms (`Float.ofInt_neg/_lt/_le`), and the reflection theorems (`Integer.toInt`, `Integer.ofInt`, round-trip + homomorphism). The fourth boundary axiom (`Float.toUInt64_of_isNatural`) and `Natural.toNat` exist only for `Provably-safe array indexing` and **are deferred with it** (past v0.7 — see ADR-0002). Not directly user-visible.
_Avoid_: "refinement-type machinery" (ambiguous), "lattice machinery"

**Refinement-type framework**:
The deferred (0.9) general system for user-defined refinements: `@refine` aliases, predicate sublanguage parser, verification phase with `omega`/`grind`. **Not in the current branch.** When the user says "refinement types" colloquially they sometimes mean this; in v0.6 work it always means the Prelude library types.
_Avoid_: bare "refinement types"

**Refinement-target mismatch**:
The case where assignability fails *and* the target is a `Prelude library type`. Two flavours:
TH0080 (literal out of range — source is a `.numberLit` outside the kind's bounds) and TH0081 (needs evidence — source is plain `number` and no narrowing or `as<T>` constructor evidence is in scope). The classifier lives in `Thales/TypeCheck/RefinementDiag.lean` as `refinementMismatch? : TSType → TSType → String → Option ThalesKind`; the two emission sites (`checkAssignable` in `Generic.lean`, `emitArgMismatch` in `Synth.lean`) call through it and supply their own TS-code fallback (TS2322 / TS2345).
_Avoid_: bare "refinement mismatch" (could be confused with lattice subtyping in `isSubtype`)

### Diagnostic vocabulary

**`TH####` codes**:
Subset/annotation violations specific to Thales. TH0001–TH0070 are subset violations (mutation, classes, `any`, non-exhaustive switch, etc.). TH0080/TH0081 are refinement-type violations (literal out of range; evidence required). TH9000–TH9003 are `@thales-expect-error` directive machinery; TH9004 is the post-emit `noSorry` check.
_Avoid_: "Thales errors" (use TH#### or "diagnostic codes")

**`TS####` codes**:
Codes mirrored from `tsc` verbatim. Thales must never invent a `TS` code; the conformance harness fails if Thales emits a `TS` code at a line `tsc` doesn't.
_Avoid_: "TypeScript errors", "tsc errors"

**Conformance harness**:
`scripts/run-examples.js` — the operational definition of Thales's correctness. Compares `tsc` and `thales` diagnostics on the accepting corpus; compares `tsx` and `lake env lean` runtime output for byte-identity.
_Avoid_: "test suite" (the harness is not a unit test framework)

### Flagged ambiguities

- **"Refinement types"** — used three different ways in conversation:
  1. The Prelude library types (the concrete `Integer`/`Natural`/`Byte`/`Bit`).
  2. The Subtype machinery on the Lean side.
  3. The Refinement-type framework (deferred to 0.9; user-defined refinements).
  When discussing the current v0.6 branch, default reading is (1); the branch ships none of (3).
