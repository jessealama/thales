// Subset-rejected example: non-boolean `if` condition (TH0026).
// tsc accepts; thales rejects because JS truthiness (`0`, `''`, `NaN`,
// `null`, `undefined` are falsy) has no Lean-side coercion — the emitted
// `if` would need a Decidable instance a Float cannot provide. Compare
// explicitly instead (`n !== 0`).
function f(n: number): number {
  // @thales-expect-error TH0026
  if (n) {
    return 1;
  }
  return 0;
}
console.log(f(2));
