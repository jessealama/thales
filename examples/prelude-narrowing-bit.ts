// Demonstrates narrowing with isBit: after the guard, the value
// flows at type Bit inside the branch.
import { Bit, isBit } from '@thales/prelude';

function negateBit(x: number): number {
  if (isBit(x)) {
    const b: Bit = x; // narrowed — no TH0081
    return 1 - b;
  }
  return x;
}

console.log(negateBit(0));
console.log(negateBit(1));
console.log(negateBit(2));
