// Subset-rejected example: number-typed value not assignable to refinement type
// without narrowing or constructor evidence (TH0081).
// tsc accepts (Integer is an alias of number); Thales rejects — no evidence.
import { Integer } from '@thales/prelude';

function wrap(n: number): Integer {
  // @thales-expect-error TH0081
  return n;
}

console.log(wrap(5));
