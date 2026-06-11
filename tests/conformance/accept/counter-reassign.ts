// #24: straight-line local reassignment lowers to `Id.run do` / `let mut`.
function inc(): number {
  let n = 0;
  n = n + 1;
  n = n + 2;
  return n;
}
console.log(inc());
