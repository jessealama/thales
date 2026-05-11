// Demonstrates asInteger succeeding: the argument is a safe integer,
// so no RangeError is thrown.
import { asInteger } from '@thales/prelude';

const n = asInteger(42);
console.log(n);
