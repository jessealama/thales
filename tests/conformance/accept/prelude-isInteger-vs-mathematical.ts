// Naming note: isInteger (prelude) means isSafeInteger, NOT Number.isInteger.
// Large powers of 2 exceed the safe integer range.
//
// Specifically: 2**53 = 9007199254740992 is mathematically an integer
// but is NOT a safe integer (it cannot be represented exactly in IEEE 754
// double precision without ambiguity with adjacent integers).
import { isInteger } from '@thales/prelude';

const big = 2 ** 53; // 9007199254740992 — one past max safe integer
console.log(Number.isSafeInteger(big)); // false
console.log(isInteger(big)); //           false — same result (isInteger = isSafeInteger)

const safe = 2 ** 53 - 1; // 9007199254740991 — max safe integer
console.log(Number.isSafeInteger(safe)); // true
console.log(isInteger(safe)); //           true
