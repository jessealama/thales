/** @throws RangeError */
function divide(a: number, b: number): number {
  if (b === 0) throw new RangeError("division by zero");
  return a / b;
}

console.log(divide(10, 2));
