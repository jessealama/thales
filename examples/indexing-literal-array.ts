// PARKED: needs Parcel 5 emit (P1/P2 indexing + proof generation).
// P1: literal indexing into a literal array. Thales lifts arr[0] from
// number | undefined to number because the index is statically in bounds.
const arr = [10, 20, 30];
const x = arr[0]; // tsc: number | undefined; Thales (post-Parcel-5): number
const z = arr[2]; // tsc: number | undefined; Thales (post-Parcel-5): number
console.log(x, z);
