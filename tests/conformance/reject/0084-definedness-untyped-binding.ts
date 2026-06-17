// Subset-rejected (TH0084): a definedness test on a body-local whose type
// the emitter cannot record (a concatenation initializer — not an
// annotation, call, element read, or literal). The emitter can neither
// fold the test (the value might be Option) nor narrow it (it might be
// non-Option), so the subset check rejects it. See #61 for generalizing
// RHS type inference, which would let this compile.
function f(a: string, b: string): string {
  const x = a + b;
  // @thales-expect-error TH0084
  if (x !== undefined) {
    return x;
  }
  return 'n';
}
console.log(f('x', 'y'));
