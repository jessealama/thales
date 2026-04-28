// Subset-rejected example: mutating array method (TH0004).
const items: number[] = [];
// @thales-expect-error TH0004
items.push(42);
console.log(items);
