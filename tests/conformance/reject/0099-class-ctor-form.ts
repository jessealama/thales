// Subset-rejected example: unsupported constructor form (TH0099) — a v1
// constructor body is a straight-line sequence of this.<field> = <expr>
// assignments.
class Gate {
  readonly level: bigint;
  // @thales-expect-error TH0099
  constructor(level: bigint) {
    if (level > 0n) {
    }
    this.level = level;
  }
}
console.log('ok');
