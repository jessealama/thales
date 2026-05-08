// Length-positive narrowing: inside `if (xs.length > 0)`, Thales lifts
// `xs[0]` from `T | undefined` to `T`.
function head(xs: number[]): number | undefined {
  if (xs.length > 0) {
    return xs[0]; // Thales: T, not T | undefined
  }
  return undefined;
}

const empty: number[] = [];
console.log(head([1, 2, 3]));
console.log(head(empty));
