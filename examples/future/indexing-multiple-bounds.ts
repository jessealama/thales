// Conjunction of multiple bounds checks: both `i < xs.length` and
// `j < xs.length` are established before `xs[i]` and `xs[j]`.
import { Natural } from '@thales/prelude';

function sumTwo(xs: number[], i: Natural, j: Natural): number | undefined {
  if (i < xs.length && j < xs.length) {
    return xs[i] + xs[j]; // Thales: number + number
  }
  return undefined;
}

console.log(sumTwo([10, 20, 30], 0 as Natural, 2 as Natural));
console.log(sumTwo([10, 20], 0 as Natural, 5 as Natural));
