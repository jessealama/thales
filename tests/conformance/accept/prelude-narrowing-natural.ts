// Demonstrates narrowing with isNatural: after the guard, the value
// flows at type Natural inside the branch.
import { Natural, isNatural } from '@thales/prelude';

function tripleIfNatural(x: number): number {
  if (isNatural(x)) {
    const n: Natural = x; // narrowed — no TH0081
    return n + n + n;
  }
  return 0;
}

console.log(tripleIfNatural(7));
console.log(tripleIfNatural(-2));
