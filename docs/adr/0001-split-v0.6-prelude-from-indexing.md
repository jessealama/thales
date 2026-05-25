# Split v0.6 into prelude (v0.6) and provably-safe indexing (later release)

**Status:** accepted (2026-05-24); **amended by ADR-0002 (2026-05-26).**

> **Amendment (ADR-0002).** Every "v0.7" reference below is superseded: v0.7
> became a 0.6-_completeness_ release and provably-safe array indexing
> (together with the `Float.toUInt64_of_isNatural` axiom and `Natural.toNat`)
> was re-deferred to a later, not-yet-fixed release. The split decision and the
> Subtype-representation decision recorded here still stand — only the target
> version for indexing changed. See ADR-0002 for the rationale.

## Context

The 56-commit branch `worktree-v0.6-subtype-refinements` implements the V2 v0.6 spec (`.claude/superpowers/specs/2026-05-07-v0.6-design.md`), which bundles two distinct features: the four built-in bounded number types (`Integer`, `Natural`, `Byte`, `Bit`) shipped via `@thales/prelude`, and provably-safe array indexing (the P1/P2 patterns that lift `arr[i] : T | undefined` to `arr[i] : T`). The bundling came out of three iterations on the same day: V0 proposed shipping just the prelude; V1 made indexing the headline and recast the prelude as "load-bearing infrastructure" for it; V2 upgraded the Lean-side representation from Float `abbrev` to true `Subtype` to close a P2 soundness gap.

## Decision

Ship the built-in bounded number types alone in v0.6. Defer provably-safe array indexing to v0.7.

The Lean-side representation stays as **Subtype** (the V2 representation, already implemented) — not Float `abbrev` (the V0 representation). The work to build the `Subtype` chain, `Coe` instances, three homomorphism boundary axioms (`Float.ofInt_neg`, `_lt`, `_le`), and reflection theorems (`Integer.toInt`/`ofInt` plus the round-trip regression test) all lands in v0.6. The fourth boundary axiom (`Float.toUInt64_of_isNatural`) and `Natural.toNat` defer to v0.7 because they exist solely to discharge P2 obligations.

The forEach/map/filter/reduce callback `index: Natural` overload ships in v0.6 even though it was added as the P3 fallback — it's a self-contained stdlib type assignment whose absence in v0.6 would be an unmotivated regression in v0.7.

## Why

The bundled release was, by the V2 spec's own estimate, 13–22 days of active work and ~25–30 new corpus fixtures. A branch that size is hard to review carefully and hard to land without integration drag. Splitting it gives two reviewable releases instead of one large one — the project's standing preference is to avoid large, unreviewable branches.

The split is asymmetric: indexing genuinely _needs_ the prelude (P2's Float-to-Nat conversion requires the non-negative + safe-integer guarantee of `Natural`), but the prelude doesn't need indexing — it stands on its own as a documentation/discipline primitive in the same family as `@throws`. The user-visible v0.6 story works without indexing: literal range checks via TH0080, evidence-required flow via TH0081, `is<T>` narrowing, throwing `as<T>` constructors, lattice coercions, and a small set of refinement-typed stdlib overloads. It's quieter than the indexing pitch but it's a real release.

Keeping the V2 (`Subtype`) representation rather than reverting to V0 (Float `abbrev`) avoids paying the V1→V2 representation-switch cost a second time when indexing ships. The `Subtype` representation is not coupled to indexing per se; it's coupled to carrying the refinement at the Lean type level, which is what makes the prelude types honest about their constraints regardless of who consumes them.

## Considered alternatives

- **Ship bundled per the V2 spec.** Rejected: too large to review carefully; the project consistently caves to bundling in design sessions and then regrets the branch size. Splitting forces the smaller-steps discipline.
- **Ship the prelude with Float `abbrev` representation (V0).** Rejected: the V2 work to upgrade to `Subtype` is done and discarding it just means redoing it in v0.7 with a representation switch and possible user-visible churn for any code that depends on Lean-side prelude internals.
- **Defer the prelude entirely and find a smaller v0.6.** Rejected: the prelude is the foundation v0.7 needs; shipping nothing now blocks v0.7 too.
