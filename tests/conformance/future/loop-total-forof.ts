// #25 + @total: Array's ForIn instance is structurally total, so a for-of
// loop passes the lake-backed termination verification as a plain `def`.
/** @total */
function product(xs: number[]): number {
  let p = 1;
  for (const x of xs) {
    p *= x;
  }
  return p;
}
console.log(product([2, 3, 4]));
