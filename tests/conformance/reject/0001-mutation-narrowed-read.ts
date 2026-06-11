// Subset-rejected example: mutation in a function that reads a
// null-tested variable outside its test (TH0001). The pure path bakes the
// null test into an Option match; do-mode's plain `if` carries no
// narrowing evidence (#40), so the whole function stays out of do-mode
// and its mutation is rejected.
function f(x: string | null): number {
  let n = 0;
  // @thales-expect-error TH0001
  n += 1;
  if (x === null) {
    return n;
  }
  return x.length;
}
console.log(f('abc'));
