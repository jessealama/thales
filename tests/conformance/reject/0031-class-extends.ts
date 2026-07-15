// Subset-rejected example: class inheritance (TH0031). Both classes are in
// the supported v1 shape; only the extends clause violates the subset.
class Animal {
  legs(): bigint {
    return 4n;
  }
}
// @thales-expect-error TH0031
class Dog extends Animal {}
console.log('ok');
