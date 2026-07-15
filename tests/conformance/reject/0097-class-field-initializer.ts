// Subset-rejected example: class field initializers (TH0097).
class Counter {
  // @thales-expect-error TH0097
  readonly start: bigint = 0n;
  constructor(start: bigint) {
    this.start = start;
  }
}
console.log('ok');
