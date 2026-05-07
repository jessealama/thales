// PARKED: needs Parcel 5 emit (Subtype-construction and narrowing-branch emit).
// Demonstrates the four prelude refinement type signatures.
// tsc sees all four as aliases of 'number'; Thales enforces the refinements.
import {
  Integer,
  Natural,
  Byte,
  Bit,
  isInteger,
  isNatural,
  isByte,
  isBit,
} from '@thales/prelude';

function describe(i: Integer, n: Natural, b: Byte, bit: Bit): string {
  return `integer=${i} natural=${n} byte=${b} bit=${bit}`;
}

const x: number = 1;
if (isInteger(x) && isNatural(x) && isByte(x) && isBit(x)) {
  console.log(describe(x, x, x, x));
}
