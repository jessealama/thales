class Animal {
  name: string;
  constructor(name: string) {
    this.name = name;
  }
  speak(): string {
    return this.name + " makes a sound";
  }
}

class Dog extends Animal {
  breed: string;
  constructor(name: string, breed: string) {
    super(name);
    this.breed = breed;
  }
}

let a: Animal = new Animal("Cat");
let d: Dog = new Dog("Rex", "Labrador");
console.log(a.name);
console.log(d.breed);
console.log(d.name);
