// Subset-rejected example: non-boolean ternary condition (TH0026).
function pick(n: number): string {
  // @thales-expect-error TH0026
  return n ? 'some' : 'none';
}
console.log(pick(3));
