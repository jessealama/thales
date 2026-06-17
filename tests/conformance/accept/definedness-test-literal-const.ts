// An un-annotated const with a literal initializer is known non-Option,
// so its definedness test folds and compiles.
function f(): string {
  const x = 'a';
  if (x !== undefined) {
    return x;
  }
  return 'b';
}
console.log(f());
