// Faithful port of npm left-pad v1.3.0 to `tsc --strict` — same algorithm:
// cached pads for the common space case, logarithmic doubling loop
// otherwise. Strictness rewrites, behavior unchanged:
//   - typed signature (subsumes the untyped `str + ''` coercion and the
//     `ch` default-and-coerce dance);
//   - `(n & 1) === 1` for truthy `if (len & 1)` (TH0026);
//   - the cache hit is bound and narrowed before use (TH0082) — for
//     n in 1..9 the hit always exists, but the type system can't see that.
const cache: string[] = [
  '',
  ' ',
  '  ',
  '   ',
  '    ',
  '     ',
  '      ',
  '       ',
  '        ',
  '         ',
];

function leftPad(str: string, len: number, ch: string): string {
  let n = len - str.length;
  if (n <= 0) {
    return str;
  }
  if (ch === ' ' && n < 10) {
    const hit = cache[n];
    if (hit !== undefined) {
      return hit + str;
    }
  }
  let pad = '';
  let c = ch;
  while (true) {
    if ((n & 1) === 1) {
      pad = pad + c;
    }
    n >>= 1;
    if (n > 0) {
      c = c + c;
    } else {
      break;
    }
  }
  return pad + str;
}

console.log(leftPad('foo', 5, ' '));
console.log(leftPad('foobar', 3, ' '));
console.log(leftPad('17', 5, '0'));
console.log(leftPad('x', 30, ' '));
console.log(leftPad('x', 20, 'ab'));
console.log(leftPad('', 9, ' '));
