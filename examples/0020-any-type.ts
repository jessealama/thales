// Subset-rejected example: explicit `any` type (TH0020).
// @thales-expect-error TH0020
function identity(x: any): any {
  return x;
}
console.log(identity(42));
