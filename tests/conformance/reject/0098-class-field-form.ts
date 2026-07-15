// Subset-rejected example: unsupported class field form (TH0098) — a v1
// class field must be declared readonly.
class Counter {
  // @thales-expect-error TH0098
  count: bigint;
  constructor(count: bigint) {
    this.count = count;
  }
}
console.log('ok');
