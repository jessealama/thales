// join/indexOf/includes lower for any receiver the emitter can statically
// resolve to number[]/string[], not just a module-level const: a body-local
// typed declarator and a typed parameter both work.
function joinLabels(): string {
  const labels: string[] = ['lo', 'hi'];
  return labels.join('/');
}

function indexIn(xs: number[]): number {
  return xs.indexOf(2);
}

console.log(joinLabels());
console.log(indexIn([3, 1, 2]));
