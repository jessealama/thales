// Subset-rejected example: non-boolean left operand of `&&` (TH0026).
function f(n: number, b: boolean): number {
  // @thales-expect-error TH0026
  if (n && b) {
    return 1;
  }
  return 0;
}
console.log(f(2, true));
