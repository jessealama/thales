// Subset-rejected example: for-of with a labeled break (TH0010).
// tsc accepts; thales rejects because labeled break/continue is outside
// the admitted loop shape (only unlabeled break and continue are supported).
function f(xs: number[]): number {
  let total = 0;
  // @thales-expect-error TH0010
  outer: for (const x of xs) {
    break outer;
  }
  return total;
}
console.log(f([1, 2, 3]));
