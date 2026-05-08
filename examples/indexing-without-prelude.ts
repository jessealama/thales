// Regression: bare `number` index does NOT lift to in-bounds — the result
// stays T | undefined. Lifting requires the Natural index type from the prelude.
// This file deliberately avoids @thales/prelude to confirm the conservative default.
function maybeAt<T>(xs: T[], i: number): T | undefined {
  if (i >= 0 && i < xs.length) {
    return xs[i]; // stays T | undefined — i is 'number', not 'Natural'
  }
  return undefined;
}

console.log(maybeAt([1, 2, 3], 1));
console.log(maybeAt([1, 2, 3], -1));
