// Subset-rejected example: explicit `unknown` type (TH0021).
// @thales-expect-error TH0021
function inspect(raw: unknown): void {
  console.log(raw);
}
inspect(42);
