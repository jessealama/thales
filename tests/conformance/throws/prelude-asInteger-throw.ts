// Demonstrates asInteger throwing a RangeError when passed a non-integer.
// tsx: prints "before", then throws RangeError (exit 1). Lean mirrors the
// throw; the harness accepts throw-iff equivalence for prelude programs.
import { asInteger } from '@thales/prelude';

console.log('before');
asInteger(3.14);
console.log('after');
