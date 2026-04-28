// Subset-rejected example: caller invokes a throwing function without
// either (a) catching in a try/catch, or (b) declaring `@throws` on
// itself (TH0060 with ThrowSource.fromCall). Every uncaught throw event
// must be visible in every signature that carries it.

/** @throws RangeError */
function parseNumber(s: string): number {
  if (s === "") throw new RangeError("empty");
  return parseFloat(s);
}

function doubleIt(s: string): number {
  // @thales-expect-error TH0060
  return parseNumber(s) * 2;
}

console.log(doubleIt("5"));
