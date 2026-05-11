// Natural-index bounds narrowing: when `i : Natural` and `i < xs.length`,
// Thales lifts `xs[i]` from `T | undefined` to `T` in the emitted Lean
// (the access becomes `xs[i.toNat]'h`, with the proof discharged by the
// enclosing `if`-guard's bounds fact). The `@ts-expect-error` below
// records that tsc rejects the arithmetic under
// `noUncheckedIndexedAccess`; Thales accepts it because of the lift.
import { Natural } from '@thales/prelude';

function doubledAt(xs: number[], i: Natural): number {
  if (i < xs.length) {
    // @ts-expect-error noUncheckedIndexedAccess: Thales lifts xs[i] to number
    return xs[i] * 2;
  }
  return 0;
}

console.log(doubledAt([10, 20, 30], 1 as Natural));
console.log(doubledAt([10, 20, 30], 5 as Natural));
