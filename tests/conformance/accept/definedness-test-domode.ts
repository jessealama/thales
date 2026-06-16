// Definedness test on a non-Option param inside a do-mode body (the local
// `out` mutation forces `Id.run do`); the vacuous test folds in do-mode too.
function f(x: string): string {
  let out = '';
  if (x !== undefined) {
    out = x;
  }
  return out;
}
console.log(f('hi'));
