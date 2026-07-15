// Subset-rejected example: non-exhaustive switch on a discriminated union
// inside a class method (TH0040) — the exhaustiveness check reaches into
// ctor/method bodies like function bodies.
type Shape = { kind: 'c'; r: bigint } | { kind: 's'; s: bigint };
class M {
  readonly z: bigint;
  constructor(z: bigint) {
    this.z = z;
  }
  pick(sh: Shape): bigint {
    // @thales-expect-error TH0040
    switch (sh.kind) {
      case 'c':
        return sh.r;
    }
    return this.z;
  }
}
console.log('ok');
