import { Integer } from '@thales/prelude';

function sumInts(...xs: Integer[]): number {
  return xs.reduce((a, b) => a + b, 0);
}

const n: number = 42;
// @thales-expect-error TH0081
sumInts(n);
