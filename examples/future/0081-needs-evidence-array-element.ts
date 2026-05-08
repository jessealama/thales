// PARKED: TH0081 in array-element context. Currently fires TS2322;
// once implemented, Thales should emit TH0081 per element.
import { Integer } from '@thales/prelude';

const n: number = 42;
// @thales-expect-error TH0081
const arr: Integer[] = [n];
console.log(arr);
