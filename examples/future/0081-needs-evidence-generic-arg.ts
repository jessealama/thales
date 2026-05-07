// PARKED: TH0081 for explicit generic type argument context not yet implemented.
// When implemented, Thales should emit TH0081 when a number flows into
// an Integer-typed generic argument position.
import { Integer } from '@thales/prelude';

function wrap<T>(x: T): T[] {
  return [x];
}

const n: number = 42;
// @thales-expect-error TH0081
const result = wrap<Integer>(n);
console.log(result);
