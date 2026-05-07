// Subset-rejected example: literal value out of range for Bit (TH0080).
// tsc accepts (Bit is an alias of number); Thales rejects — 2 is not 0 or 1.
import { Bit } from '@thales/prelude';

// @thales-expect-error TH0080
const b: Bit = 2;
console.log(b);
