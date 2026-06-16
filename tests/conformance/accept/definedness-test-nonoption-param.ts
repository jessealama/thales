// A definedness test on a non-Option parameter is vacuous (the value is
// always defined); it folds to the taken branch and compiles.
function f(x: string): string {
  if (x === null) {
    return 'never';
  }
  return x;
}
console.log(f('hi'));
