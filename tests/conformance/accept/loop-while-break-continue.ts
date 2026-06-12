// #26: unlabeled break/continue inside `while` map 1:1 to Lean's break and
// continue — Lean's `while` re-checks the condition on continue, matching TS.
function sumOddsBelow(limit: number): number {
  let sum = 0;
  let n = 0;
  while (true) {
    n += 1;
    if (n >= limit) {
      break;
    }
    if (n % 2 === 0) {
      continue;
    }
    sum += n;
  }
  return sum;
}
console.log(sumOddsBelow(10));
console.log(sumOddsBelow(1));
