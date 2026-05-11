// PARKED: TH0081 for rest-parameter call context.
// Currently fires TH0081 correctly but the function body (using .reduce)
// triggers TS2339 because Array methods aren't fully in Thales's subset.
// When Array methods are supported, this fixture can move to examples/.
import { Integer } from '@thales/prelude';

function sumInts(...xs: Integer[]): number {
  return xs.reduce((a, b) => a + b, 0);
}

const n: number = 42;
// @thales-expect-error TH0081
sumInts(n);
