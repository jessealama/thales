// Generic call expressions
function identity<T>(x: T): T {
  return x;
}
let a: number = identity<number>(42);
let b: string = identity<string>('hello');

// Generic classes (via companion interface)
interface Box<T> {
  value: T;
}
class Box<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}
let numBox: Box<number> = new Box<number>(42);

// keyof
interface Point {
  x: number;
  y: number;
}
type PointKeys = keyof Point;
let k: PointKeys = 'x';

// Index access types
type PointX = Point['x'];
let px: PointX = 42;

// Enum branding
enum Color {
  Red,
  Green,
  Blue,
}
let c: Color = Color.Red;

// Output
console.log(a);
console.log(b);
console.log(k);
console.log(px);
console.log(c);
