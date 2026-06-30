// Top-level mutation + for-of (issue #49): accepted and compiles, prints 6.
let total = 0;
for (const x of [1, 2, 3]) {
  total += x;
}
console.log(total);
