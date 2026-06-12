// Subset-rejected example: for-of over a string parameter (TH0010).
// tsc accepts string iteration; Thales rejects because the admitted for-of
// shape requires the iterable to resolve to an array type. A string produces
// 1-char string elements in TS but Lean would bind c : Char — the types
// differ and lone-surrogate handling diverges.
function count(s: string): number {
  let n = 0;
  // @thales-expect-error TH0010
  for (const c of s) {
    n += 1;
  }
  return n;
}
console.log(count('hello'));
