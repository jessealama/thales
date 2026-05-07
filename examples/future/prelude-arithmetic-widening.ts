// PARKED: needs Parcel 5 emit (Subtype-construction and narrowing-branch emit).
// Demonstrates arithmetic widening: Integer + number → number in v0.6.
// Recovery requires a guard or constructor call.
import { Integer, isInteger } from '@thales/prelude';

const x: number = 10;
if (isInteger(x)) {
  const i: Integer = x;
  const sum: number = i + 1; // widened to number — narrowing lost
  console.log(sum);
}
