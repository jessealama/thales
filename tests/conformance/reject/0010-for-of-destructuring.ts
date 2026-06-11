// Subset-rejected example: for-of with destructuring binding (TH0010).
// tsc accepts; thales rejects because array-destructuring in the for-of
// binding is outside the admitted loop shape.
function f(pairs: [number, number][]): number {
  let total = 0;
  // @thales-expect-error TH0010
  for (const [a, b] of pairs) {
    total += 0;
  }
  return total;
}
console.log(
  f([
    [1, 2],
    [3, 4],
  ]),
);
