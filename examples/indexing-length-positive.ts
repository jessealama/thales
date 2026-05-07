// P2: length-positive narrowing. If xs.length > 0, then xs[0] is in bounds.
// Thales lifts xs[0] from T | undefined to T inside the branch.
function head(xs: number[]): number | undefined {
  if (xs.length > 0) {
    return xs[0]; // Thales (post-Parcel-5): T, not T | undefined
  }
  return undefined;
}

const empty: number[] = [];
console.log(head([1, 2, 3]));
console.log(head(empty));
