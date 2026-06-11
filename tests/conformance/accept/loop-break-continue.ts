// #25: unlabeled break/continue map 1:1 to Lean do-notation's break and
// continue inside `for … in … do`.
function sumEvensUntilNegative(xs: number[]): number {
  let total = 0;
  for (const x of xs) {
    if (x < 0) {
      break;
    }
    if (x % 2 !== 0) {
      continue;
    }
    total += x;
  }
  return total;
}
console.log(sumEvensUntilNegative([2, 3, 4, -1, 8]));
