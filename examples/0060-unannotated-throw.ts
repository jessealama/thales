// Subset-rejected example: function body contains `throw` without a
// `@throws` annotation (TH0060). Thales makes exception effects visible
// in types; a function that throws must declare what it throws.

function divide(a: number, b: number): number {
  if (b === 0) {
    // @thales-expect-error TH0060
    throw new RangeError("zero");
  }
  return a / b;
}

console.log(divide(10, 2));
