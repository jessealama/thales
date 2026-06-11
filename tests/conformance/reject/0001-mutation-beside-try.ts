// Subset-rejected example: mutation in a function containing try/catch (TH0001).
// tsc accepts; thales rejects: the exception path emits pure Except
// match-chains, which do-mode mutation cannot thread through (#41) — a
// try/catch anywhere in the body keeps the whole function out of do-mode.
// (Mutation INSIDE the try is the separate TH0007.)
/** @throws RangeError */
function half(x: number): number {
  if (x < 0) {
    throw new RangeError('negative');
  }
  return x / 2;
}
function f(x: number): number {
  let n = 0;
  // @thales-expect-error TH0001
  n = 5;
  try {
    return half(x);
  } catch (e) {
    return n;
  }
}
console.log(f(4));
