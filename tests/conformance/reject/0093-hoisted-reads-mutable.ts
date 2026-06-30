// TH0093: a hoisted function reads a top-level mutable `let`. The `let` is
// lowered into the `main` IO do-block (a `let mut`), so a hoisted `def report`
// elaborated outside `main` cannot see it. Out of v1 scope.
let total = 0;
for (const x of [1, 2, 3]) {
  total += x;
}
// @thales-expect-error TH0093
function report(): number {
  return total;
}
console.log(report());
