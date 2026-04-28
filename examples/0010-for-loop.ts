// Subset-rejected example: while loop (TH0010).
// @thales-expect-error TH0010
while (false) {
  console.log("unreachable");
}
