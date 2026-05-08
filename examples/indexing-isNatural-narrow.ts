// Manual narrowing via isNatural conjunction. `isNatural(i) && i < xs.length`
// establishes both the Natural typing and the in-bounds fact in one condition.
import { isNatural } from '@thales/prelude';

function maybeAt<T>(xs: T[], i: number): T | undefined {
  if (isNatural(i) && i < xs.length) {
    return xs[i]; // Thales: T (both Natural and in-bounds)
  }
  return undefined;
}

console.log(maybeAt(['a', 'b', 'c'], 1));
console.log(maybeAt(['a', 'b', 'c'], -1));
console.log(maybeAt(['a', 'b', 'c'], 5));
