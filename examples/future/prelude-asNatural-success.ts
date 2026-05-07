// PARKED: needs Parcel 5 emit (Subtype-construction and narrowing-branch emit).
// Demonstrates asNatural succeeding: non-negative integer argument.
import { asNatural } from '@thales/prelude';

const n = asNatural(7);
console.log(n);
