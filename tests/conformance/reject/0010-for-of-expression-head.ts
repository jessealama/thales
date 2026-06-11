// Subset-rejected example: for-of with expression (non-declaration) head (TH0010).
// tsc accepts; thales rejects because the admitted for-of shape requires a
// const/let declaration binding, not a bare assignment target.
function f(xs: number[]): void {
  let x = 0;
  // @thales-expect-error TH0010
  for (x of xs) {
    console.log(x);
  }
}
f([1, 2, 3]);
