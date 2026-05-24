// Subset-rejected example: literal value out of range for Integer (TH0080).
// tsc accepts (Integer is an alias of number); Thales rejects — 2^53 exceeds max safe integer.
import { Integer } from '@thales/prelude';

// @thales-expect-error TH0080
const n: Integer = 9007199254740992;
console.log(n);
