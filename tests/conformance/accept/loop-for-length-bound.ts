// #25: canonical C-style for bounded by `arr.length`. The bound identifier
// is never reassigned in the body (the miscompile guard: JS re-evaluates
// `i < xs.length` each iteration, a Lean range fixes the bound at entry).
function indexWeight(xs: number[]): number {
  let total = 0;
  for (let i = 0; i < xs.length; i++) {
    total += i;
  }
  return total;
}
console.log(indexWeight([7, 8, 9]));
