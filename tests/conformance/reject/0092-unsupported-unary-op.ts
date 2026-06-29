// Subset-rejected example: `typeof`, `void`, and `delete` are not supported
// anywhere (TH0092) — neither in value position nor inside a guard. A `typeof`
// test such as `typeof x === "string"` is rejected just like any other use.

// @thales-expect-error TH0092
const t = typeof 1;
// @thales-expect-error TH0092
const u = void 0;

const obj: { a?: number } = { a: 1 };
// @thales-expect-error TH0092
const removed = delete obj.a;

function f(x: string): boolean {
  // @thales-expect-error TH0092
  if (typeof x === 'string') {
    return true;
  }
  // @thales-expect-error TH0092
  if (typeof x !== 'string') {
    return false;
  }
  return false;
}

console.log(t);
console.log(u);
console.log(f('a'));
