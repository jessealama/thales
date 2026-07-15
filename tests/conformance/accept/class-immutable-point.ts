class Point {
  readonly x: bigint;
  readonly y: bigint;
  constructor(x: bigint, y: bigint) {
    this.x = x;
    this.y = y;
  }
  norm1(): bigint {
    const ax = this.x < 0n ? -this.x : this.x;
    const ay = this.y < 0n ? -this.y : this.y;
    return ax + ay;
  }
  translate(dx: bigint, dy: bigint): Point {
    return new Point(this.x + dx, this.y + dy);
  }
}
const p = new Point(3n, -4n);
console.log(p.norm1());
const q = p.translate(1n, 1n);
console.log(q.x, q.y);
