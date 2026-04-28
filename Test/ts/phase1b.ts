// Phase 1b comprehensive test

// Enum declarations
enum Color { Red, Green, Blue }
enum Direction { Up = "UP", Down = "DOWN", Left = "LEFT", Right = "RIGHT" }

// Generic function
function identity<T>(x: T): T {
  return x;
}

// Generic interface
interface Box<T> {
  value: T;
  label?: string;
}

// Generic type alias
type Pair<A, B> = [A, B];

// Type alias with function type
type Transform = (input: number) => string;

// Type alias with object literal type
type Config = { debug: boolean; verbose: boolean };

// Type alias with tuple type
type Point3D = [number, number, number];

// Declare statements (erased)
declare function externalApi(x: number): string;
declare const API_KEY: string;

// Function with optional and rest params
function greet(name: string, greeting?: string, ...tags: string[]): string {
  let g: string = greeting as string;
  if (g === undefined) {
    g = "Hello";
  }
  return g + ", " + name;
}

// Using enums
let c: Color = Color.Red;
console.log(c);
console.log(Color.Blue);

// Using generics
console.log(identity(42));
console.log(identity("hello"));

// Using as expression
let x: any = 123;
let y: number = x as number;
console.log(y);

// Optional param call
console.log(greet("world"));
console.log(greet("world", "Hi"));
