// A function that both mutates a local and reads a null-tested parameter
// outside its test — formerly rejected wholesale (the #40-era conservatism)
// because do-mode's plain `if` carried no narrowing evidence. Do-mode now
// lowers the null test to a statement-position match whose some-arm
// rebinds `x` at the narrowed type, so the mutation is eligible and the
// read is sound.
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
