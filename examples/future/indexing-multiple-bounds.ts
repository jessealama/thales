// PARKED: needs Parcel 5 emit (P1/P2 indexing + proof generation).
// P2: conjunction of multiple bounds checks. Both i < xs.length and j < xs.length
// are established before accessing xs[i] and xs[j].
import { Natural } from '@thales/prelude';

function sumTwo(xs: number[], i: Natural, j: Natural): number | undefined {
  if (i < xs.length && j < xs.length) {
    return xs[i] + xs[j]; // Thales (post-Parcel-5): number + number
  }
  return undefined;
}

console.log(sumTwo([10, 20, 30], 0 as Natural, 2 as Natural));
console.log(sumTwo([10, 20], 0 as Natural, 5 as Natural));
