// Subset-rejected example: non-boolean `if` condition (TH0026).
// JS truthiness has no Lean-side coercion; compare explicitly (`n !== 0`).
function f(n: number): number {
  // @thales-expect-error TH0026
  if (n) {
    return 1;
  }
  return 0;
}
console.log(f(2));
