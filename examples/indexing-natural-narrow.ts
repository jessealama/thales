// PARKED: needs Parcel 5 emit (P1/P2 indexing + proof generation).
// P2: Natural-index bounds narrowing. If i < xs.length and i : Natural,
// then xs[i] is in bounds. Thales lifts xs[i] from T | undefined to T.
import { Natural } from '@thales/prelude';

function safeAt<T>(xs: T[], i: Natural): T | undefined {
  if (i < xs.length) {
    return xs[i]; // Thales (post-Parcel-5): T, not T | undefined
  }
  return undefined;
}

console.log(safeAt([10, 20, 30], 1 as Natural));
console.log(safeAt([10, 20, 30], 5 as Natural));
