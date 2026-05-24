// PARKED: needs Parcel 5 emit (Subtype-construction and narrowing-branch emit).
// Demonstrates narrowing with isByte: after the guard, the value
// flows at type Byte inside the branch.
import { Byte, isByte } from '@thales/prelude';

function doubleIfByte(x: number): number {
  if (isByte(x)) {
    const b: Byte = x; // narrowed — no TH0081
    return b + b;
  }
  return 0;
}

console.log(doubleIfByte(100));
console.log(doubleIfByte(300));
