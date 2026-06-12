// Subset-rejected example: non-canonical C-style for whose body has a
// loop-level `continue` (TH0010). The while-desugared lowering would skip
// the update clause on `continue`, where TS runs it before re-testing —
// so this shape stays rejected. (Without the `continue`, `i += 2` updates
// have been admitted via the #26 while-desugar.)
function f(): number {
  let total = 0;
  // @thales-expect-error TH0010
  for (let i = 1; i <= 5; i += 2) {
    if (i === 3) {
      continue;
    }
    total += i;
  }
  return total;
}
console.log(f());
