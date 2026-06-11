// Mirror-of-tsc example: assignment RHS must be assignable to the
// variable's declared type (here the widened initializer type, number).
// Both tsc and thales report TS2322 at the assignment line.
function f(): number {
  let n = 0;
  n = 'not a number';
  return n;
}
console.log(f());
