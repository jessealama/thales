// This file should type-check cleanly (no errors)
let x: number = 42;
let y: string = "hello";
let z: boolean = true;

function add(a: number, b: number): number {
  return a + b;
}

let result: number = add(1, 2);
console.log(result);
console.log(x);
console.log(y);
console.log(z);
