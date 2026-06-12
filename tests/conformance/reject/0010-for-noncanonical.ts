// Subset-rejected example: non-canonical C-style for loop (TH0010).
// tsc accepts; thales rejects because the admitted C-style for shape
// requires `i++` as the update expression; `i += 2` is non-canonical.
function f(): number {
  let total = 0;
  // @thales-expect-error TH0010
  for (let i = 1; i <= 5; i += 2) {
    total += i;
  }
  return total;
}
console.log(f());
