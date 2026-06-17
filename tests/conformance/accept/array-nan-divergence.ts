// indexOf uses strict ===, so it never matches NaN; includes uses
// SameValueZero, so it does. (Unblocked by NaN now lowering to a Float value.)
const xs: number[] = [NaN, 1];
console.log(xs.indexOf(NaN));
console.log(xs.includes(NaN));
