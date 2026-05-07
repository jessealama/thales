// PARKED: needs Parcel 5 emit (P1/P2 indexing + proof generation).
// P2: recursion with a Natural index. sumFrom accumulates arr[i] + arr[i+1] + ...
// The Natural index ensures non-negativity; the bounds check ensures in-range.
import { Natural, isNatural } from '@thales/prelude';

function sumFrom(arr: number[], i: Natural): number {
  if (i < arr.length) {
    const next = i + 1;
    if (isNatural(next)) {
      return arr[i] + sumFrom(arr, next); // Thales (post-Parcel-5)
    }
    return arr[i];
  }
  return 0;
}

console.log(sumFrom([1, 2, 3, 4], 0 as Natural));
