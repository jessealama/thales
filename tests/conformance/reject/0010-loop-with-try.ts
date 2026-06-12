// Subset-rejected example: for-of loop in a function that also contains
// try/catch (TH0010). tsc accepts; thales rejects because the loop shape
// is not admitted; the try/catch does not produce a separate diagnostic.
function f(xs: number[]): number {
  let total = 0;
  // @thales-expect-error TH0010
  for (const x of xs) {
    total += x;
  }
  try {
    return total;
  } catch (e) {
    return 0;
  }
}
console.log(f([1, 2, 3]));
