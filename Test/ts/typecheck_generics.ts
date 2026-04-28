// Generic function with inference
function identity<T>(x: T): T {
  return x;
}

let n: number = identity(42);
let s: string = identity("hello");

// Generic type alias
type Pair<A, B> = [A, B];
let p: Pair<string, number> = ["hi", 1];

// Generic interface
interface Box<T> {
  value: T;
}

let b: Box<number> = { value: 42 };

// Array inference: T[] matched against number[]
function first<T>(arr: T[]): T {
  return arr[0];
}

let f: number = first([1, 2, 3]);

// Output
console.log(n);
console.log(s);
console.log(f);
