// #24: bitwise and % compound assignment, desugared through the
// JS-semantics runtime helpers (#32).
function mask(): number {
  let bits = 0;
  bits |= 5;
  bits &= 6;
  bits ^= 3;
  bits <<= 2;
  bits %= 7;
  return bits;
}
console.log(mask());
