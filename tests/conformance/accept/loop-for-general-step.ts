// #26: a non-canonical C-style `for` (non-zero start, `>`, compound step)
// lowers via while-desugaring: init, then `while test do { body; update }`.
function sumDown(n: number): number {
  let total = 0;
  for (let i = n; i > 0; i -= 2) {
    total += i;
  }
  return total;
}
console.log(sumDown(9));
console.log(sumDown(0));
