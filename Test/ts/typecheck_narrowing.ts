// Control-flow narrowing tests — this file should type-check cleanly

// typeof narrowing: string
function typeofString(x: string | number): void {
  if (typeof x === "string") {
    let s: string = x;
    console.log(s);
  } else {
    let n: number = x;
    console.log(n);
  }
}

// typeof narrowing: number
function typeofNumber(x: string | number): void {
  if (typeof x === "number") {
    let n: number = x;
    console.log(n);
  }
}

// Truthiness narrowing: removes null
function truthiness(x: string | null): void {
  if (x) {
    let s: string = x;
    console.log(s);
  }
}

// Equality narrowing: x === null
function eqNull(x: string | null): void {
  if (x === null) {
    let n: null = x;
    console.log(n);
  }
}

// Equality narrowing: x !== null (negated)
function neqNull(x: string | null): void {
  if (x !== null) {
    let s: string = x;
    console.log(s);
  }
}

// Negation: !(typeof x === "string")
function negation(x: string | number): void {
  if (!(typeof x === "string")) {
    let n: number = x;
    console.log(n);
  }
}

// Compound: && narrows both variables
function compoundAnd(x: string | number, y: string | null): void {
  if (typeof x === "string" && typeof y === "string") {
    let s1: string = x;
    let s2: string = y;
    console.log(s1);
    console.log(s2);
  }
}

// Compound: || in else branch
function compoundOr(x: string | number): void {
  if (typeof x === "string" || typeof x === "number") {
    console.log(x);
  }
}

// instanceof narrowing
class Dog {
  breed: string;
  constructor(breed: string) {
    this.breed = breed;
  }
}

function instanceofNarrow(x: Dog | string): void {
  if (x instanceof Dog) {
    console.log(x);
  }
}

typeofString("hello");
typeofNumber(42);
truthiness("test");
eqNull(null);
neqNull("test");
negation(42);
compoundAnd("hello", "world");
compoundOr("test");
instanceofNarrow(new Dog("Labrador"));
