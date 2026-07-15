// Subset-rejected example: a class method referencing a later-declared
// method (TH0101) — methods may only reference earlier methods
// (self-recursion is allowed).
class Chain {
  first(): bigint {
    // @thales-expect-error TH0101
    return this.second();
  }
  second(): bigint {
    return 1n;
  }
}
console.log('ok');
