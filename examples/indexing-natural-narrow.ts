// Natural-index bounds narrowing: when `i : Natural` and `i < xs.length`,
// Thales lifts `xs[i]` from `T | undefined` to `T`.
import { Natural } from '@thales/prelude';

function safeAt<T>(xs: T[], i: Natural): T | undefined {
  if (i < xs.length) {
    return xs[i]; // Thales: T, not T | undefined
  }
  return undefined;
}

console.log(safeAt([10, 20, 30], 1 as Natural));
console.log(safeAt([10, 20, 30], 5 as Natural));
