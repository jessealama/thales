// PARKED: needs Parcel 5 emit (Subtype-construction and narrowing-branch emit).
// Edge case: -0 is admitted as Bit (isBit(-0) === true because -0 === 0 in JS).
// This is a consequence of how IEEE 754 defines -0.
import { Bit, isBit } from '@thales/prelude';

const negZero = -0;
if (isBit(negZero)) {
  const b: Bit = negZero; // narrowed from number to Bit — no TH0081
  console.log(b === 0); // true: -0 === 0 in JS
}
