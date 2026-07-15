// Subset-rejected example: a class method used as a value (TH0102) —
// methods may only be called, never read as values.
class Point {
  readonly x: bigint;
  constructor(x: bigint) {
    this.x = x;
  }
  norm1(): bigint {
    return this.x < 0n ? -this.x : this.x;
  }
}
const p = new Point(3n);
// @thales-expect-error TH0102
const f = p.norm1;
console.log('ok');
