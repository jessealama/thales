// A function-call receiver type-checks under `tsc`, but the emitter cannot
// statically resolve its element type, so join is out of the Thales subset.
function getArr(): number[] {
  return [3, 1, 2];
}
// @thales-expect-error TH0085
console.log(getArr().join(','));
