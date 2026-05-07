// PARKED: needs Parcel 5 emit (Subtype-construction and narrowing-branch emit).
// Demonstrates asInteger throwing a RangeError when passed a non-integer.
// tsx: prints "before", then throws RangeError (exit 1).
// Lean (post-Parcel-5): mirrors the throw behavior.
// Parcel 4 status: harness accepts throw-iff equivalence for prelude programs.
import { asInteger } from '@thales/prelude';

console.log('before');
asInteger(3.14);
console.log('after');
