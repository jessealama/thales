// Subset-rejected example: C-style for loop where the bound array is mutated
// inside the body (TH0010). tsc accepts; thales rejects because reassigning
// the array variable used as the length bound poisons the loop shape.
// Only TH0010 fires: a rejected loop is not recursed into, so the xs = ys
// assignment inside the body never reaches the mutation router.
function f(xs: number[], ys: number[]): void {
  // @thales-expect-error TH0010
  for (let i = 0; i < xs.length; i++) {
    xs = ys;
  }
}
f([1, 2, 3], [4, 5, 6]);
