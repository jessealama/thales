// Recursion with a Natural index: sumFrom accumulates arr[i] + arr[i+1] + …
// The Natural index gives non-negativity; the bounds check gives in-range.
import { Natural, isNatural } from '@thales/prelude';

function sumFrom(arr: number[], i: Natural): number {
  if (i < arr.length) {
    const next = i + 1;
    if (isNatural(next)) {
      return arr[i] + sumFrom(arr, next);
    }
    return arr[i];
  }
  return 0;
}

console.log(sumFrom([1, 2, 3, 4], 0 as Natural));
