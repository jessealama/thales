// Subset-rejected example: non-boolean `while` test (TH0026).
// Loop tests are condition positions like `if`: a number operand relies on
// JS truthiness (0 and NaN are falsy), which has no Lean-side coercion.
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
