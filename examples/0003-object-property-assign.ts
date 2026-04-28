// Subset-rejected example: object property assignment (TH0003).
const pt = { x: 1, y: 2 };
// @thales-expect-error TH0003
pt.x = 10;
console.log(pt);
