// Subset-rejected example: a constructor referencing a same-class method
// (TH0101) — `ctor'` is emitted before every method, so any such reference
// is a forward reference, including via another instance.
class Cell {
  readonly x: bigint;
  constructor(o: Cell) {
    // @thales-expect-error TH0101
    this.x = o.bump();
  }
  bump(): bigint {
    return 1n;
  }
}
console.log('ok');
