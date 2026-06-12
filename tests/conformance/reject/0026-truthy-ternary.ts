// Subset-rejected example: non-boolean ternary condition (TH0026).
// The ternary test is a condition position; a number operand relies on JS
// truthiness (0 and NaN are falsy). Compare explicitly instead (`n !== 0`).
function pick(n: number): string {
  // @thales-expect-error TH0026
  return n ? 'some' : 'none';
}
console.log(pick(3));
