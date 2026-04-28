// Subset-rejected example: async function (TH0012).
// @thales-expect-error TH0012
async function compute(): Promise<number> {
  return 42;
}
