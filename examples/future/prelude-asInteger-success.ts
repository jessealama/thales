// PARKED: needs Parcel 5 emit (Subtype-construction and narrowing-branch emit).
// Demonstrates asInteger succeeding: the argument is a safe integer,
// so no RangeError is thrown.
import { asInteger } from '@thales/prelude';

const n = asInteger(42);
console.log(n);
