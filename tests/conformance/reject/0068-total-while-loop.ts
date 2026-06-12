// Subset-rejected example: `while` loop inside a `@total` function (TH0068).
// tsc accepts; thales rejects because the loop's Lean lowering is backed by
// a partial combinator that is opaque to the termination verifier — the
// `@total` claim cannot be checked. Use a for-of loop or recursion, or drop
// `@total`.
/** @total */
function drain(n: number): number {
  let i = n;
  // @thales-expect-error TH0068
  while (i > 0) {
    i -= 1;
  }
  return i;
}
console.log(drain(3));
