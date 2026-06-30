interface Inner {
  v: bigint;
}
interface Outer {
  inner: Inner;
  tag: bigint;
}

function build(v: bigint): Outer {
  return { inner: { v }, tag: 7n };
}

const o = build(5n);
console.log(o.inner.v);
console.log(o.tag);
