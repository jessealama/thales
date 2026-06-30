// #91: TH0093 must not fire on an object-literal key or a non-computed member
// property name that merely shares a name with a top-level mutated `let`. The
// key `total` in `{ total: 99n }` (inside the hoisted `makeBox`) and the
// property `total` in `makeBox().total` (inside the hoisted `const first`) are
// not references to the outer mutable `total`. tsc accepts; this must emit.
interface Box {
  total: bigint;
}
let total = 0;
for (const x of [1, 2, 3]) {
  total += x;
}
function makeBox(): Box {
  return { total: 99n };
}
const first: bigint = makeBox().total;
console.log(first);
console.log(total);
