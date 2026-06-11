// Subset-rejected example: for-of over a body-declared array (TH0010).
// tsc accepts; Thales rejects because for-of admission is conservative —
// the bindingEnv only contains typed parameters, not body-declared locals,
// so `ys` does not resolve to an array type in the for-of RHS check.
// This is not a semantic hazard; widening to body-declared arrays is a
// future task.
function f(): number {
  const ys: number[] = [1, 2, 3];
  let t = 0;
  // @thales-expect-error TH0010
  for (const y of ys) {
    t += y;
  }
  return t;
}
console.log(f());
