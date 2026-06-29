// Subset-rejected example: undiscriminated primitive union (TH0022). A
// `string | number` parameter shares no discriminant, so thales has no Lean
// representation for it. (Telling the two apart at runtime would need `typeof`,
// which is itself outside the subset — see TH0092.)
// @thales-expect-error TH0022
function describe(x: string | number): string {
  return 'value';
}
console.log(describe(21));
