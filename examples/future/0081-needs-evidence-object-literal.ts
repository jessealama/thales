// PARKED: TH0081 in object-literal property context. Currently fires
// TS2322; once implemented, Thales should emit TH0081 instead.
import { Integer } from '@thales/prelude';

const n: number = 42;
// @thales-expect-error TH0081
const obj: { i: Integer } = { i: n };
console.log(obj);
