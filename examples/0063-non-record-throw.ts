// Subset-rejected example: throwing a non-record primitive (TH0063).
// Thrown values must be record types so their fields are nameable in
// the emitted Lean pattern match.

/** @throws string */
function parseOrFail(s: string): number {
  // @thales-expect-error TH0063
  if (s === '') throw 'empty string';
  return parseFloat(s);
}

console.log(parseOrFail('42'));
