// Subset-rejected example: TH0081 in variable declaration context.
// Assigning a plain number to an Integer-typed const without evidence.
import { Integer } from '@thales/prelude';

const n: number = 42;
// @thales-expect-error TH0081
const x: Integer = n;
console.log(x);
