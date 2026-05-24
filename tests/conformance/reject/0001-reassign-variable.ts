// Subset-rejected example: variable reassignment (TH0001).
// tsc accepts; thales rejects because locals are immutable in v1.
let counter = 0;
// @thales-expect-error TH0001
counter = counter + 1;
console.log(counter);
