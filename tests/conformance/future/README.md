# Parked fixtures

The `.ts` files in this directory are valid programs against the
intended Thales subset, but the current compiler cannot fully check or
emit them. They live here so the design intent is captured in source
form, and so that work that unparks them has a concrete target.

The conformance harness (`scripts/run-examples.js`) does not visit this
directory: every fixture under `tests/conformance/{accept,reject,throws}/`
is run, every fixture here is skipped. Once a fixture works end-to-end,
move it into the appropriate bucket.

If you are adding a feature that should make a parked fixture pass, the
workflow is:

1. Get the fixture passing by hand:
   `timeout 60 .lake/build/bin/thales tests/conformance/future/<name>.ts`
   followed by
   `timeout 60 lake env lean <Name>.lean`.
2. `git mv tests/conformance/future/<name>.ts tests/conformance/accept/<name>.ts`
   (or `reject/` / `throws/`, depending on the contract the fixture is meant to satisfy).
3. Run the harness: `timeout 1200 npm run conformance`.
4. Make sure prettier is happy: `timeout 60 npm run format -- tests/conformance/`.

## What's currently parked

- `0081-default-value.ts`, `0081-generic-arg.ts`,
  `0081-class-property.ts`, `0081-spread-arg.ts` — additional contexts
  in which a plain `number` should be rejected as unassignable to a
  refinement type. v0.6 fires TH0081 at variable declarations, function
  parameters, and return statements only.
- `prelude-math-abs.ts` — `Math.abs` overloaded to return `Natural` for an
  `Integer` argument; needs Subtype-construction and narrowing-branch emit
  (see the fixture's header).
