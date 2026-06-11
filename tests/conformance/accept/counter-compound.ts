// #24's headline example: ++ and compound assignment desugar to
// `x = x OP y` and lower through `Id.run do`.
function count(): number {
  let n = 0;
  n++;
  n += 2;
  return n;
}
// The arithmetic compound family; values chosen to stay within the
// runtime's number-formatting subset (no >6-decimal results).
function scale(): number {
  let m = 10;
  m -= 1;
  m *= 4;
  m /= 8;
  m **= 2;
  return m;
}
console.log(count());
console.log(scale());
