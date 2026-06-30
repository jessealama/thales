// Output order is preserved across the hoist boundary (issue #49): a, 6, b.
console.log('a');
const base = 3;
let total = 0;
for (const x of [1, 2, 3]) {
  total += x;
}
console.log(total);
console.log('b');
