// Subset-rejected example: class expressions (TH0030).
// @thales-expect-error TH0030
const Counter = class {
  tick(): bigint {
    return 1n;
  }
};
console.log('ok');
