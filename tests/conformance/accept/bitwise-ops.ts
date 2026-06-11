// JS bitwise and % semantics (#32): operands truncate to 32-bit integers
// (ToInt32/ToUint32), shift counts mask to 5 bits, % keeps the dividend's
// sign. Expected values are Node's output.
console.log(5 & 3);
console.log(5 | 3);
console.log(5 ^ 3);
console.log(1 << 4);
console.log(-16 >> 2);
console.log(-16 >>> 28);
console.log(5.7 & 3);
console.log(7 % 3);
console.log(-7 % 3);
console.log(5.5 % 2);
