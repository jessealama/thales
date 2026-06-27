// Subset-rejected example: typeof/void in value position are not supported (TH0092).
// @thales-expect-error TH0092
const t = typeof 1;
// @thales-expect-error TH0092
const u = void 0;
console.log(t);
console.log(u);
