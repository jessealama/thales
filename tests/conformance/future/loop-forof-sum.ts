// #25: for-of accumulation — the canonical do-mode loop. `total` is an
// initialized let mutated in the loop body; lowers to `for x in xs do`.
function sum(xs: number[]): number {
  let total = 0;
  for (const x of xs) {
    total += x;
  }
  return total;
}
console.log(sum([1, 2, 3, 4]));
