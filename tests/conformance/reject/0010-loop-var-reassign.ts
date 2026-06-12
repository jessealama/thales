// Subset-rejected example: for-of loop variable reassigned inside body (TH0010).
// tsc accepts; thales rejects because mutating the loop binding variable
// is outside the admitted for-of shape.
function f(xs: number[]): number {
  let total = 0;
  // @thales-expect-error TH0010
  for (let x of xs) {
    x = x + 1;
    total += x;
  }
  return total;
}
console.log(f([1, 2, 3]));
