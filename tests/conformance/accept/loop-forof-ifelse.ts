// #25 × #24: if/else branches inside a loop body — mutation in a branch
// stays visible after it, per do-notation statement semantics.
function clampedSum(xs: number[]): number {
  let total = 0;
  for (const x of xs) {
    if (x > 10) {
      total += 10;
    } else {
      total += x;
    }
  }
  return total;
}
console.log(clampedSum([3, 12, 5]));
