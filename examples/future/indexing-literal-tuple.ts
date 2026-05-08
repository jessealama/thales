// P1: literal indexing into a tuple type.
// tup[1] is 'number' (from the tuple type), not 'number | undefined'.
const tup: [string, number, boolean] = ['hello', 42, true];
const s = tup[0]; // string
const n = tup[1]; // number
const b = tup[2]; // boolean
console.log(s, n, b);
