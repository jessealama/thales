// Subset-rejected example: TH0081 in return statement context.
// Returning a plain number from a function declared to return Integer.
import { Integer } from '@thales/prelude';

function unsafeWrap(n: number): Integer {
  // @thales-expect-error TH0081
  return n;
}

console.log(unsafeWrap(7));
