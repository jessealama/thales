// #91: TH0093 must not fire when a hoisted function merely binds a parameter
// that shadows a top-level mutated `let`. The `total` read inside `bump` is the
// parameter, not a free reference to the outer mutable `total`, so the hoisted
// `def bump` is self-contained. tsc accepts; this must emit and run.
let total = 0;
for (const x of [1, 2, 3]) {
  total += x;
}
function bump(total: number): number {
  return total + 1;
}
console.log(bump(10));
console.log(total);
