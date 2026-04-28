// This file should produce type errors
let x: number = "hello";
let y: string = 42;

function add(a: number, b: number): number {
  return a + b;
}

add("x", 2);
add(1);

unknownFunc();

console.log("this line is fine");
