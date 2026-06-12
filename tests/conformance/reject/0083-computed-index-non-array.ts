// Subset-rejected example: computed index access on a non-array (TH0083).
// JS string indexing (`s[0]`) and object bracket access are out of subset;
// arrays are the only indexable values.
function firstChar(s: string): string | undefined {
  // @thales-expect-error TH0083
  return s[0];
}
console.log(firstChar('abc'));
