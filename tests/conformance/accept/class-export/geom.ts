export class Point {
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

class Hidden {
  readonly tag: bigint;
  constructor(tag: bigint) {
    this.tag = tag;
  }
  bump(): bigint {
    return this.tag + 1n;
  }
}

export function originPlus(dx: bigint, dy: bigint): Point {
  return new Point(0n, 0n).translate(dx, dy);
}
