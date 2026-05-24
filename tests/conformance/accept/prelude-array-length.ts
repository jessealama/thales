// PARKED: needs Parcel 5 emit (Subtype-construction and narrowing-branch emit).
// Demonstrates Array.length typed as Natural — always non-negative.
import { Natural } from '@thales/prelude';

const arr = [10, 20, 30];
const len: Natural = arr.length; // Natural, not number
console.log(len);
