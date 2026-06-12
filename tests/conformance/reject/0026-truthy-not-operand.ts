// Subset-rejected example: `!` on a non-boolean operand (TH0026).
function f(n: number): number {
  // @thales-expect-error TH0026
  if (!n) {
    return 1;
  }
  return 0;
}
console.log(f(0));
