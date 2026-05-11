# Parked examples

The `.ts` files in this directory are valid programs against the
intended Thales subset, but the current compiler cannot fully check or
emit them. They live here so the design intent is captured in source
form, and so that work that unparks them has a concrete target.

The conformance harness (`scripts/run-examples.js`) does not visit this
directory: every fixture in `examples/` proper is run, every fixture
here is skipped. Once a fixture works end-to-end, it gets moved up one
level into `examples/`.

If you are adding a feature that should make a parked fixture pass, the
workflow is:

1. Get the fixture passing by hand:
   `timeout 60 .lake/build/bin/thales examples/future/<name>.ts`
   followed by
   `timeout 60 lake env lean <Name>.lean`.
2. `git mv examples/future/<name>.ts examples/<name>.ts`.
3. Run the harness: `timeout 1200 node scripts/run-examples.js`.
4. Make sure prettier is happy: `timeout 60 npm run format -- examples/`.

## What's currently parked (v0.6)

- `indexing-foreach.ts` — forEach-callback indexing (P3). Needs
  arrow-function type-checking, contextual bound threading, an
  `arr.forEach` emit lowering, and a witness derivation from the
  iteration framework. Targeting 0.8.
- `indexing-literal-tuple.ts` — tuple indexing as a provably-total
  access. Needs the existing tuple lowering to admit `tup[k]` form.
- `indexing-multiple-bounds.ts`, `indexing-recursion.ts` — exercise
  `noUncheckedIndexedAccess` patterns that Thales' type-checker does
  not yet reproduce.
- `indexing-out-of-bounds.ts`, `prelude-arithmetic-widening.ts`,
  `prelude-edge-negative-zero.ts`, `prelude-signatures.ts` — use
  top-level `if` statements; the emitter currently only handles
  top-level declarations and bare expressions.
- `0081-array-element.ts`, `0081-default-value.ts`,
  `0081-generic-arg.ts`, `0081-object-literal.ts`,
  `0081-class-property.ts`, `0081-rest-param.ts`,
  `0081-spread-arg.ts` — additional contexts in which a plain `number`
  should be rejected as unassignable to a refinement type. v0.6 fires
  TH0081 at variable declarations, function parameters, and return
  statements only.
