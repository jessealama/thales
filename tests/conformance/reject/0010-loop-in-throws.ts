// Subset-rejected example: for-of loop inside a @throws-annotated function (TH0010).
// tsc accepts; thales rejects because the loop shape is not admitted even
// when the enclosing function carries a @throws annotation.
/** @throws RangeError */
function f(xs: number[]): number {
  let total = 0;
  // @thales-expect-error TH0010
  for (const x of xs) {
    if (x < 0) {
      throw new RangeError('negative');
    }
    total += x;
  }
  return total;
}
console.log(f([1, 2, 3]));
