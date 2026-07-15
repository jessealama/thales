// Subset-rejected example: method overload signatures (TH0100) — the
// signature and the implementation parse as two same-named methods, and a
// class member name may be declared only once.
class C {
  m(a: bigint): bigint;
  // @thales-expect-error TH0100
  m(a: bigint): bigint {
    return a;
  }
}
console.log('ok');
