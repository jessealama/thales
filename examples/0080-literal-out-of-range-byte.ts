// Subset-rejected example: literal value out of range for refinement type (TH0080).
// tsc accepts (Byte is an alias of number); Thales rejects — 256 exceeds [0, 255].
import { Byte } from '@thales/prelude';

// @thales-expect-error TH0080
const b: Byte = 256;
console.log(b);
