// Subset-rejected example: class accessors (TH0094).
class Temperature {
  // @thales-expect-error TH0094
  get celsius(): bigint {
    return 0n;
  }
}
console.log('ok');
