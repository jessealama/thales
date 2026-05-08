// Literal indexing into a literal array. Thales lifts `arr[0]` from
// `number | undefined` to `number` because the index is statically in bounds.
const arr = [10, 20, 30];
const x = arr[0]; // tsc: number | undefined; Thales: number
const z = arr[2]; // tsc: number | undefined; Thales: number
console.log(x, z);
