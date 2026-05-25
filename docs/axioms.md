# Axioms in the Thales runtime

`Thales.TS.Runtime` postulates twelve `axiom`s. They all encode
properties of IEEE-754 doubles (Lean's `Float`) and the conversions
between `Float`, `Nat`, and `Int` that the compiler relies on to give
the built-in bounded number types their soundness story.

Lean's standard library treats `Float` as opaque from the elaborator's
point of view: arithmetic does not reduce in the kernel, and the stdlib
ships only a handful of `Float` lemmas, none of which cover the
IEEE-754 boundary properties we need. Mathlib does not currently fill
the gap either. We therefore postulate the missing facts as axioms,
with each one accompanied by an inline comment giving the IEEE-754
justification. They are stable assumptions about a fixed, well-specified
floating-point format, not open conjectures.

The source of truth is
[`Thales/TS/Runtime.lean`](../Thales/TS/Runtime.lean); this document
groups the axioms by purpose and explains what relies on each.

## What "axiom" vs "sorry" means here

Every emitted Lean file is conformance-checked for `sorry` or `sorryAx`
and rejected on a hit (TH9004). The runtime is held to the same bar:
no `sorry`s in `Thales/`. The `axiom`s below are deliberate, named
postulates with documented justifications — not bailed-out proofs. If a
proof obligation arises that we genuinely expect to be provable but
cannot discharge in the pinned toolchain, the policy is to mark it
`sorry` and let TH9004 surface it as a tracked follow-up; it is **not**
to disguise it as an axiom. Anything declared `axiom` in the runtime is
something we are choosing to trust.

## Group 1 — Float ↔ Int boundary

Soundness basis for `Integer.ofInt`, `Integer.toInt`, and the
in-range `Int` ↔ `Float` round-trip.

| Axiom                       | Statement                                                | Used by                                                          |
| --------------------------- | -------------------------------------------------------- | ---------------------------------------------------------------- |
| `Nat.toFloat_isSafeInteger` | `n ≤ 2^53 − 1` ⇒ `n.toFloat` is a safe integer.          | `Integer.ofInt` (witness for the non-negative branch)            |
| `Float.neg_isSafeInteger`   | Negating a safe-integer Float preserves `isSafeInteger`. | `Integer.ofInt` (witness for the negative branch)                |
| `Nat.toFloat_nonneg`        | `n.toFloat ≥ 0.0` for every `Nat n`.                     | Length lifters (`Array.toNaturalSize`, `String.toNaturalLength`) |
| `Float.ofInt_neg`           | `(Integer.ofInt (-n)).val = -((Integer.ofInt n).val)`.   | Reflection of negation                                           |
| `Float.ofInt_lt`            | `(Integer.ofInt m).val < (Integer.ofInt n).val ↔ m < n`. | Reflection of `<`                                                |
| `Float.ofInt_le`            | `(Integer.ofInt m).val ≤ (Integer.ofInt n).val ↔ m ≤ n`. | Reflection of `≤`                                                |

The three homomorphism axioms (`ofInt_neg`, `_lt`, `_le`) were
validated against the `feat/thales-grind-poc` branch before v0.6
landed.

A seventh boundary axiom (`Float.toUInt64_of_isNatural`,
asserting that an `isNatural` Float round-trips through
`Float → UInt64 → Nat → Float`) will ship alongside `Natural.toNat`
and provably-safe array indexing — both re-deferred past v0.7, which
became a 0.6-completeness release (see ADR-0002).

## Group 2 — `Float.abs`

Soundness basis for the `Math.abs(Integer): Natural` overload.

| Axiom                     | Statement                          | Used by                         |
| ------------------------- | ---------------------------------- | ------------------------------- |
| `Float.abs_isSafeInteger` | `isInteger x` ⇒ `isInteger x.abs`. | `Math.absI : Integer → Natural` |
| `Float.abs_nonneg`        | `x.abs ≥ 0.0`.                     | `Math.absI`                     |

## Group 3 — Integer reflection

Round-trip and arithmetic homomorphisms used by emitted code that
reasons about safe-integer arithmetic at the Lean level.

| Axiom                      | Statement                                                                                       |
| -------------------------- | ----------------------------------------------------------------------------------------------- |
| `Integer.toInt_ofInt`      | `(Integer.ofInt n h).toInt = n`.                                                                |
| `Integer.add_homomorphism` | When `x.val + y.val` is a safe integer, `Integer.toInt ⟨x.val + y.val, _⟩ = x.toInt + y.toInt`. |
| `Integer.sub_homomorphism` | Same shape for `-`.                                                                             |
| `Integer.mul_homomorphism` | Same shape for `*`.                                                                             |

These four are postulated rather than proven because each statement
reduces, after `unfold`ing, to a fact about `Float.toUInt64.toNat ∘
Nat.toFloat` round-trips and IEEE-754 add/sub/mul exactness on
safe-integer inputs — internals Lean's stdlib does not expose. The
spec's V2 §9 explicitly authorizes expanding the boundary-axiom set
when proofs from the existing axioms are not constructible in the
pinned toolchain.

## What you are trusting

If you depend on Thales-emitted Lean for downstream reasoning, you are
trusting (in addition to Lean's own kernel and stdlib) twelve
statements about IEEE-754 doubles within the safe-integer range. They
are mechanically simple and rest on a well-specified standard, but they
are postulated, not derived inside Lean. The corresponding TS-side
runtime values are exercised end-to-end by the conformance corpus, so a
mistake in any of these axioms would also have to survive byte-identity
testing against a standards-compliant V8.

`Test/Emit/RefinementReflectionTest.lean` references each axiom and
each derived theorem by name; renaming or removing one of them breaks
the test, which keeps the surface honest.

## Future direction

There are three plausible paths to shrinking this set:

1. **Mathlib catches up.** If Mathlib eventually ships IEEE-754
   `Float` reasoning, the boundary axioms collapse to lemma calls.
2. **Prove the reflection axioms from the boundary axioms.** The
   four reflection axioms (Group 3) ought to follow from the boundary
   axioms (Group 1) plus a small amount of `Float.toUInt64`/`Nat.toFloat`
   theory. The proofs are tractable but not cheap and were deferred for
   v0.6.
3. **Replace `Float`-as-axiomatized with a verified `Float64` model.**
   This would let the boundary axioms become lemmas at the cost of a
   substantially larger runtime. Out of scope for the foreseeable
   future.

None of these change the surface visible to a Thales user.
