// PARKED: needs Parcel 5 emit (Subtype-construction and throw propagation).
// Demonstrates asBit throwing: 2 is not a bit (not 0 or 1).
import { asBit } from '@thales/prelude';

console.log('before');
asBit(2);
console.log('after');
