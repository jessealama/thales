// Subset-rejected example: for-of over a function-call iterable (TH0010).
// tsc accepts; thales rejects because the admitted for-of shape requires the
// iterable to be a simple identifier (a local array variable), not a call expression.
function make(): number[] {
  return [1, 2, 3];
}
function f(): number {
  let total = 0;
  // @thales-expect-error TH0010
  for (const x of make()) {
    total += x;
  }
  return total;
}
console.log(f());
