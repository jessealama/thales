// Mutation of a local alongside a null-tested parameter read outside its
// test: the null test lowers to a statement-position match whose some-arm
// rebinds `x` at the narrowed type, keeping the mutation eligible.
function f(x: string | null): number {
  let n = 0;
  n += 1;
  if (x === null) {
    return n;
  }
  return x.length;
}
console.log(f('abc'));
console.log(f(null));
