// PARKED: TH0081 for spread argument context not yet implemented.
// Currently the spread gives TS2554 (wrong argument count); Parcel 3
// didn't implement refinement checking at spread sites.
import { Integer } from '@thales/prelude';

function add(a: Integer, b: Integer): number {
  return a + b;
}

const nums: number[] = [1, 2];
// @thales-expect-error TH0081
add(...nums);
