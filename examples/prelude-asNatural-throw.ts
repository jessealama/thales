// Demonstrates asNatural throwing: -1 is not a natural number.
import { asNatural } from '@thales/prelude';

console.log('before');
asNatural(-1);
console.log('after');
