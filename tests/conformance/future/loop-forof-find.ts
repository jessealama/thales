// #25: a loop with no mutation at all — early `return` out of the loop is
// do-notation's native early return, and the loop itself must trigger
// do-mode entry (the pure path cannot host a loop).
function contains(xs: number[], target: number): boolean {
  for (const x of xs) {
    if (x === target) {
      return true;
    }
  }
  return false;
}
console.log(contains([1, 2, 3], 2));
console.log(contains([1, 2, 3], 5));
