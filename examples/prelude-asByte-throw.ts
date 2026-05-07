// PARKED: needs Parcel 5 emit (Subtype-construction and throw propagation).
// Demonstrates asByte throwing: 256 exceeds the byte range [0, 255].
import { asByte } from '@thales/prelude';

console.log('before');
asByte(256);
console.log('after');
