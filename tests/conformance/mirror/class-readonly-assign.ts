class Point {
  readonly x: bigint;
  constructor(x: bigint) {
    this.x = x;
  }
}
const p = new Point(1n);
p.x = 5n;
