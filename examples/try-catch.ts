/** @throws RangeError */
function mustDivide(a: number, b: number): number {
  if (b === 0) throw new RangeError('zero');
  return a / b;
}

function safeDivide(a: number, b: number): number {
  try {
    return mustDivide(a, b);
  } catch (e) {
    return 0;
  }
}

console.log(safeDivide(10, 2));
console.log(safeDivide(10, 0));
