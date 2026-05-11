// PARKED: needs Parcel 5 emit (Subtype-construction and narrowing-branch emit).
// Demonstrates string.length typed as Natural — always non-negative.
import { Natural } from '@thales/prelude';

const greeting = 'hello';
const len: Natural = greeting.length; // Natural, not number
console.log(len);
