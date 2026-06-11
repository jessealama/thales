// Subset-rejected example: mutating a variable whose narrowing the
// emitter relies on (TH0001) — undefined tests count the same as null
// tests (#42), since the emitter lowers `string | undefined` to Option
// and bakes the test into its match/if lowering.
function f(x: string | undefined): number {
  if (x === undefined) {
    // @thales-expect-error TH0001
    x = 'fallback';
  }
  return x.length;
}
console.log(f('word'));
