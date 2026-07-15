// Subset-rejected example: private class members (TH0096).
class Vault {
  // @thales-expect-error TH0096
  private secret: bigint;
  constructor(secret: bigint) {
    this.secret = secret;
  }
}
console.log('ok');
