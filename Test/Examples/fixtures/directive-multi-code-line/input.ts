// @thales-expect-error TH0030
class Animal {}
// @thales-expect-error TH0031
class Dog extends Animal {}
console.log(new Dog() instanceof Animal);
