// PARKED: TH0081 for array-element context not yet implemented.
// Currently fires TS2322 instead; Parcel 3 didn't cover this context.
// When implemented, Thales should emit TH0081 for each element.
import { Integer } from '@thales/prelude';

const n: number = 42;
// @thales-expect-error TH0081
const arr: Integer[] = [n];
console.log(arr);
