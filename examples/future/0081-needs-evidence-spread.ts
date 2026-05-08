// PARKED: TH0081 in spread-argument context. Currently fires TS2554
// (wrong argument count); once implemented, refinement checking should
// fire here.
import { Integer } from '@thales/prelude';

function add(a: Integer, b: Integer): number {
  return a + b;
}

const nums: number[] = [1, 2];
// @thales-expect-error TH0081
add(...nums);
