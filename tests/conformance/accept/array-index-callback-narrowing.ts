// Element-read narrowing inside an inline callback: the parameter is
// contextually typed, so the emitter has no recorded type for `hit` and
// the narrowing match must fire without one.
function apply(callback: (xs: number[]) => number): number {
  return callback([1, 2]);
}

const result = apply((xs) => {
  const hit = xs[0];
  if (hit !== undefined) {
    return hit;
  }
  return 42;
});
console.log(result);
