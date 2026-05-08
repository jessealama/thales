// Demonstrates Math.abs overloaded to return Natural when given an Integer.
import { Integer, Natural, isInteger } from '@thales/prelude';

function absOfInteger(x: number): Natural | undefined {
  if (isInteger(x)) {
    const i: Integer = x;
    const result: Natural = Math.abs(i); // overloaded: Integer → Natural
    return result;
  }
  return undefined;
}

console.log(absOfInteger(-7));
console.log(absOfInteger(3.14));
