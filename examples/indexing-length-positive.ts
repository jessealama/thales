// Length-positive narrowing: inside `if (xs.length > 0)`, Thales lifts
// `xs[0]` from `T | undefined` to `T` in the emitted Lean (the access
// becomes `xs[0]'h`, with a non-emptiness witness from the guard).
function headPlusOne(xs: number[]): number {
  if (xs.length > 0) {
    // @ts-expect-error noUncheckedIndexedAccess: Thales lifts xs[0] to number
    return xs[0] + 1;
  }
  return 0;
}

console.log(headPlusOne([10, 20, 30]));
console.log(headPlusOne([]));
