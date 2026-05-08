// PARKED: TH0081 at default-parameter-value sites. Once implemented,
// Thales should emit TH0081 for the default expression.
import { Integer } from '@thales/prelude';

const someNumber: number = 5;

// @thales-expect-error TH0081
function withDefault(i: Integer = someNumber): Integer {
  return i;
}

console.log(withDefault());
