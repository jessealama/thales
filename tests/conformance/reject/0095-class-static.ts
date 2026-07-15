// Subset-rejected example: static class members (TH0095).
class Registry {
  // @thales-expect-error TH0095
  static count(): bigint {
    return 0n;
  }
}
console.log('ok');
