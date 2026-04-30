// Subset-rejected example: intersection type (TH0023).
type Named = { name: string };
type Aged = { age: number };
// @thales-expect-error TH0023
type Person = Named & Aged;
const p: Person = { name: 'Alice', age: 30 };
console.log(p.name);
