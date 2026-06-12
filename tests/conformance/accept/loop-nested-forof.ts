// #25: nested admitted loops — the inner for-of recurses through the same
// do-mode lowering as the outer.
function crossSum(xs: number[], ys: number[]): number {
  let total = 0;
  for (const x of xs) {
    for (const y of ys) {
      total += x * y;
    }
  }
  return total;
}
console.log(crossSum([1, 2], [10, 20]));
