// Subset-rejected example: switch shape with no Lean lowering (TH0041).
// tsc accepts; thales rejects because the emitter lowers exactly one
// switch shape — a discriminated-union field dispatch with all-return
// arms. A plain-identifier scrutinee used to be silently dropped from
// the emitted Lean (#44).
function f(x: string): number {
  // @thales-expect-error TH0041
  switch (x) {
    case 'a':
      return 1;
    case 'b':
      return 2;
  }
  return 0;
}
console.log(f('a'));
