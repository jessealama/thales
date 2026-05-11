// Literal indexing into a literal array: Thales lifts each access to
// `number` in the emitted Lean (the proof is decidable, discharged with
// `by native_decide`). tsc with `noUncheckedIndexedAccess` would reject
// the addition because each operand is possibly undefined.
const arr = [10, 20, 30];
// @ts-expect-error noUncheckedIndexedAccess: Thales lifts arr[k] to number
console.log(arr[0] + arr[2]);
