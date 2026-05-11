/** @throws TypeError | RangeError */
function parse(s: string): number {
  if (s === '') throw new TypeError('empty string');
  const n = parseFloat(s);
  if (isNaN(n)) throw new RangeError('not a number');
  return n;
}

console.log(parse('42'));
