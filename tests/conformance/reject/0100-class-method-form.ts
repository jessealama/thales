// Subset-rejected example: unsupported class method form (TH0100) — a v1
// method needs an explicit return type annotation.
class Counter {
  // @thales-expect-error TH0100
  zero() {
    return 0n;
  }
}
console.log('ok');
