// Subset-rejected example: binding the name `undefined` (TH0103) — the
// emitter lowers the `undefined` global to `.none`, so a user binding
// named `undefined` has no Lean image.
function f(): number {
  // @thales-expect-error TH0103
  const undefined = 5;
  return undefined;
}
// @thales-expect-error TH0103
function g(undefined: number): number {
  return undefined;
}
console.log(f() + g(1));
