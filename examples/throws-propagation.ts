/** @throws RangeError */
function parseNumber(s: string): number {
  if (s === "") throw new RangeError("empty");
  return parseFloat(s);
}

/** @throws RangeError */
function addParsed(a: string, b: string): number {
  const x = parseNumber(a);
  const y = parseNumber(b);
  return x + y;
}

try {
  console.log(addParsed("1", "2"));
} catch (e) {
  console.log("caught error");
}
