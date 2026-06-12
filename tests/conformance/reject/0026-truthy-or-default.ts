// Subset-rejected example: `||` as a truthy default outside a condition
// position (TH0026) — the operands themselves must be boolean.
function pick(s: string): string {
  // @thales-expect-error TH0026
  return s || 'fallback';
}
console.log(pick(''));
