// PARKED: needs Parcel 5 emit (P1/P2 indexing + proof generation).
// P2: manual narrowing via isNatural conjunction. The conjunction
// `isNatural(i) && i < xs.length` establishes both the Natural typing
// and the in-bounds fact in a single condition.
import { isNatural } from '@thales/prelude';

function maybeAt<T>(xs: T[], i: number): T | undefined {
  if (isNatural(i) && i < xs.length) {
    return xs[i]; // Thales (post-Parcel-5): T (both Natural and in-bounds)
  }
  return undefined;
}

console.log(maybeAt(['a', 'b', 'c'], 1));
console.log(maybeAt(['a', 'b', 'c'], -1));
console.log(maybeAt(['a', 'b', 'c'], 5));
