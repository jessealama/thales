// `join`/`indexOf`/`includes` type-check on any array under `tsc`, but Thales
// lowers them only for `number[]`/`string[]` receivers. An identifier whose
// element type is anything else (a `boolean[]`, a nested `number[][]`, …) is
// out of the Thales subset: emitting it would produce uncompilable Lean.
const bs: boolean[] = [true, false];
// @thales-expect-error TH0085
console.log(bs.includes(true));

const xss: number[][] = [[1], [2]];
// @thales-expect-error TH0085
console.log(xss.join(','));
