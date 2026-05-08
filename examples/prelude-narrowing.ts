// Demonstrates narrowing with isInteger: after the guard, the value
// flows at type Integer inside the branch.
import { Integer, isInteger } from '@thales/prelude';

function doubleIfInteger(x: number): number {
  if (isInteger(x)) {
    const i: Integer = x; // narrowed — no TH0081
    return i + i;
  }
  return 0;
}

console.log(doubleIfInteger(21));
console.log(doubleIfInteger(3.14));
