// Subset-rejected example: module-level variable reassignment (TH0001).
// tsc accepts; thales rejects because top-level bindings stay immutable —
// only function-local non-escaping mutation is in the subset (#24).
let counter = 0;
// @thales-expect-error TH0001
counter = counter + 1;
console.log(counter);
