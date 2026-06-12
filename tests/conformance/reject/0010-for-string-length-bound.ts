// Subset-rejected example: canonical C-style for bounded by a string's
// .length (TH0010). tsc accepts; thales rejects because the length-bound
// identifier must be an array-typed parameter — the Lean range loop needs
// Array.size (a Nat), and String length semantics diverge (UTF-16 code
// units in JS vs codepoints in Lean).
function f(s: string): number {
  let t = 0;
  // @thales-expect-error TH0010
  for (let i = 0; i < s.length; i++) {
    t += i;
  }
  return t;
}
console.log(f('abc'));
