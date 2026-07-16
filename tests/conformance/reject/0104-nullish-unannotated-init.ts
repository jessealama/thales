// Subset-rejected example: a bare `null`/`undefined` initializer with no
// type annotation (TH0104) — nothing pins the Option's element type, so
// the lowered `.none` cannot elaborate.
// @thales-expect-error TH0104
const u = undefined;
// @thales-expect-error TH0104
const n = null;
console.log('ok');
