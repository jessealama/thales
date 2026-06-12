// Subset-rejected example: non-boolean `while` test (TH0026).
// Compare explicitly instead (`k !== 0` or `k > 0`).
function countdown(n: number): number {
  let k = n;
  let steps = 0;
  // @thales-expect-error TH0026
  while (k) {
    k -= 1;
    steps += 1;
  }
  return steps;
}
console.log(countdown(3));
