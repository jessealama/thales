import { Integer } from '@thales/prelude';

const n: number = 42;
// @thales-expect-error TH0081
const obj: { i: Integer } = { i: n };
console.log(obj);
