// Subset-rejected example: class inheritance (TH0031; co-emits TH0030).
// @thales-expect-error TH0030
class Animal {}
// @thales-expect-error TH0031
class Dog extends Animal {}
console.log(new Dog() instanceof Animal);
