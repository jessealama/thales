// Subset-rejected example: non-boolean right operand of `||` (TH0026).
function isPos(n: number): boolean {
  return n > 0;
}
function g(n: number): number {
  // @thales-expect-error TH0026
  if (isPos(n) || n) {
    return 1;
  }
  return 0;
}
console.log(g(2));
