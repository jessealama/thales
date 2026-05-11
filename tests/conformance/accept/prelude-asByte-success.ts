// Demonstrates asByte succeeding: argument is in [0, 255].
import { asByte } from '@thales/prelude';

const b = asByte(200);
console.log(b);
