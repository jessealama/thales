// Subset-rejected example: assignment in expression position (TH0006).
// tsc accepts; thales treats mutation as a statement-level effect only.
function f(): number {
  let n = 0;
  // @thales-expect-error TH0006
  const y = (n = 1);
  return y;
}
console.log(f());
