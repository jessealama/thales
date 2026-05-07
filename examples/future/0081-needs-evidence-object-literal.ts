// PARKED: TH0081 for object-literal property context not yet implemented.
// Currently fires TS2322 instead; Parcel 3 didn't cover this context.
// When implemented, Thales should emit TH0081 instead of TS2322.
import { Integer } from '@thales/prelude';

const n: number = 42;
// @thales-expect-error TH0081
const obj: { i: Integer } = { i: n };
console.log(obj);
