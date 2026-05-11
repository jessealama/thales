// Two accesses to the same lifted index. Both `xs[i]` reads emit as
// `xs[i.toNat]'h` with the bounds proof from the enclosing `if`, so
// the addition flows as plain `number + number`. Under tsc +
// `noUncheckedIndexedAccess` each operand is possibly undefined and
// the `+` is rejected.
import { Natural } from '@thales/prelude';

function symmetricSum(xs: number[], i: Natural): number {
  if (i < xs.length) {
    // @ts-expect-error noUncheckedIndexedAccess: Thales lifts xs[i] to number
    return xs[i] + xs[i];
  }
  return 0;
}

console.log(symmetricSum([10, 20, 30], 1 as Natural));
console.log(symmetricSum([10, 20, 30], 5 as Natural));
