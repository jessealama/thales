// #26: `while` lowers to Lean do-notation `while`. The left-pad milestone
// shape: condition re-reads mutated state each iteration.
function leftPad(str: string, len: number, ch: string): string {
  let pad = str;
  while (pad.length < len) {
    pad = ch + pad;
  }
  return pad;
}
console.log(leftPad('7', 3, '0'));
console.log(leftPad('hello', 3, '*'));
