type Shape = { kind: 'c'; r: bigint } | { kind: 's'; s: bigint };

class Meter {
  readonly scale: bigint;
  constructor(scale: bigint) {
    this.scale = scale;
  }
  measure(sh: Shape): bigint {
    switch (sh.kind) {
      case 'c':
        return sh.r * this.scale;
      case 's':
        return sh.s * this.scale;
    }
  }
}
const m = new Meter(2n);
console.log(m.measure({ kind: 'c', r: 3n }));
console.log(m.measure({ kind: 's', s: 5n }));
