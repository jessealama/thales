// Subset-rejected example: mutation inside try/catch (TH0007).
// tsc accepts; thales rejects because the exception path emits pure
// Except match-chains, which do-mode mutation cannot thread through yet.
function f(x: number): number {
  let n = 0;
  try {
    // @thales-expect-error TH0007
    n = x;
  } catch (e) {
    return 0;
  }
  return n;
}
console.log(f(2));
