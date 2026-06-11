// #24 + @total: `Id.run do` without loops is total, so the lake-backed
// termination verification accepts a mutating body as a plain `def`.
/** @total */
function count(): number {
  let n = 0;
  n++;
  n += 2;
  return n;
}
console.log(count());
