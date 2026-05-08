// Stepwise narrowing: an outer `if (isNatural(i))` narrows `i` to
// `Natural`, then an inner `if (i < xs.length)` adds the in-bounds
// fact, lifting `xs[i]` to `T` in the emitted Lean. Bind the lifted
// value and use it twice — under tsc + `noUncheckedIndexedAccess`,
// `v` is `number | undefined` and the multiplication errors; Thales
// emits the access via the bounds proof so `v` flows as `number`.
import { isNatural } from '@thales/prelude';

function squaredAt(xs: number[], i: number): number {
  if (isNatural(i)) {
    if (i < xs.length) {
      // @ts-expect-error noUncheckedIndexedAccess: Thales lifts xs[i] to number
      const v: number = xs[i];
      return v * v;
    }
  }
  return -1;
}

console.log(squaredAt([10, 20, 30], 1));
console.log(squaredAt([10, 20, 30], -1));
console.log(squaredAt([10, 20, 30], 5));
