# Re-sequence 0.7 as a 0.6-completeness release; re-defer indexing

**Status:** accepted (2026-05-26). Amends ADR-0001, which had deferred
provably-safe array indexing *to* v0.7.

## Context

ADR-0001 split the bundled v0.6 spec into a prelude release (v0.6, shipped)
and provably-safe array indexing (targeted at v0.7). `CHANGELOG.md`, the
`Provably-safe array indexing` and `Subtype machinery` glossary entries in
`CONTEXT.md`, and code comments in `Builtins.lean` all subsequently named
v0.7 as the indexing release.

Reviewing the actual 0.6 shipped state surfaced three features that are
already *inside the subset* but incomplete:

- `Array.map` / `Array.reduce` return `any` (no callback-return inference),
  and `any` is rejected by SubsetCheck — so array transforms are
  effectively unusable in the subset today.
- TH0081 (refinement evidence required) fires at only 3 of its intended
  positions.
- Top-level `if` statements don't lower (only declarations and bare
  expressions do), forcing a function wrapper and leaving several prelude
  fixtures parked.

## Decision

Make v0.7 a **completeness release**: `map`/`reduce` return inference (inline
arrow / function-expression callbacks, monomorphic), TH0081 at two further
positions (object-literal property values and array-literal elements), and
top-level `if`. Its defining property is that it adds **no new language
surface** — every item finishes a feature already in the subset.

Re-defer all provably-safe array indexing (P1/P2/tuple/P3), the seventh
boundary axiom (`Float.toUInt64_of_isNatural`), and `Natural.toNat` to a
later release. Sequencing of indexing against Arc-1 work (loops / local
mutation) is left open.

## Why

- **The arcs are meant to alternate.** `docs/future.md` frames Thales as two
  arcs — meet TypeScript halfway (Arc 1) and bring proofs to TS (Arc 2) —
  advancing in alternation. v0.6 was an Arc-2 release (refinement
  infrastructure); indexing is also Arc-2 (it consumes the prelude to
  discharge proof obligations). Shipping it next would be two Arc-2 releases
  back-to-back while basic "real TypeScript" gaps remain unaddressed.
- **A completeness release is structurally low-risk.** Adding no new language
  surface is the most direct answer to the recurring over-scoping problem
  ADR-0001 was itself created to manage. It cannot balloon the way a
  new-theme branch can.
- **The scope is self-limiting and was pruned during planning.** TH0081's
  default-value and generic-argument positions were trimmed because they
  require parser+AST schema changes to capture syntax the parser currently
  discards (leaving only the two pure-routing positions); spread-argument
  TH0081 additionally needs spread-into-call semantics (new surface);
  class-property TH0081 is unreachable while classes are TH0030; `map`/
  `reduce` inference is capped at inline monomorphic callbacks.
- **Indexing reads better after loops exist.** Every P2 fixture in the
  indexing spec is contorted into recursion because loops are TH0010. The
  idiomatic consumer of bounds-checked indexing is a counted `for` loop.
  Re-deferring keeps open the option to land loops (Arc 1) first, so indexing
  arrives with natural idioms instead of recursion stand-ins.

## Considered alternatives

- **Ship P1 indexing only in 0.7.** Honors the prior commitment with a small
  branch (static-length, `decide`-discharged, no new axiom) but continues
  Arc 2 and delivers the least-felt half of the indexing pain point.
- **Ship full P1+P2 indexing in 0.7 as planned.** The headline feature, but
  lands a new soundness-critical axiom plus narrowing and dependent-if emit
  machinery in one branch — the size ADR-0001 split things to avoid.
- **Pivot 0.7 to Arc 1 (loops / local mutation).** Closes the most
  fundamental gap, but `Id.run do` + `mut` + break/continue + aliasing is
  itself an over-scoping risk; deferred in favour of the lower-risk
  completeness release.

## Consequences

- The prelude's `arr.length: Natural` and `forEach`-index:`Natural` overloads
  (shipped in 0.6 as load-bearing infrastructure for indexing) remain unused
  by their intended consumer for another release.
- ADR-0001's "indexing → v0.7" target is superseded; its split decision and
  its Subtype-representation decision stand.
- Within 0.7 there is a build-order dependency: `map`/`reduce` inference must
  land before the `0081-rest-param` fixture can move out of `future/`, since
  that fixture's body uses `reduce`.
