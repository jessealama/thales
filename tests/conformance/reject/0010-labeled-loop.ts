// Subset-rejected example: label-wrapped for-of loop without labeled break (TH0010).
// tsc accepts; Thales rejects because `emitBodyDo` has no labeledStmt lowering.
// A label on a loop is poisoned wholesale (hasUnloweredLoopShape) regardless of
// whether a labeled break or continue appears in the body. This is distinct from
// 0010-labeled-break.ts which tests the labeled-break-inside-body case.
function f(xs: number[]): number {
  let t = 0;
  // @thales-expect-error TH0010
  outer: for (const x of xs) {
    t += x;
  }
  return t;
}
console.log(f([1, 2, 3]));
