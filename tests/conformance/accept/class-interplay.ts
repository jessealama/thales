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
  doubled(): Point {
    return this.translate(this.x, this.y);
  }
  marchRight(steps: bigint): Point {
    return steps <= 0n ? this : this.translate(1n, 0n).marchRight(steps - 1n);
  }
}

class Pair {
  readonly a: bigint;
  readonly b: bigint;
  constructor(a: bigint, b: bigint) {
    this.a = a;
    this.b = b;
  }
}

interface Box {
  p: Point;
}

function furthest(a: Point, b: Point): Point {
  return a.norm1() < b.norm1() ? b : a;
}

const p = new Point(3n, -4n);
const q: Pair = { a: 1n, b: 2n };
const boxed: Box = { p: new Point(1n, 2n) };
const far = furthest(p, boxed.p);
const walked = far.marchRight(2n);
console.log(p.norm1(), boxed.p.norm1());
console.log(q.a, q.b);
console.log(far.x, far.y);
console.log(walked.x, walked.y, walked.doubled().x);
