// Subset-rejected example: literal value out of range for Natural (TH0080).
// tsc accepts (Natural is an alias of number); Thales rejects — 2^53 exceeds max safe integer.
import { Natural } from '@thales/prelude';

// @thales-expect-error TH0080
const n: Natural = 9007199254740992;
console.log(n);
