// Union subtyping
let a: string | number = 'hello';
let b: string | number = 42;

function handle(x: string | number): void {
  console.log(x);
}
handle('test');
handle(123);

// Object structural subtyping
interface Point {
  x: number;
  y: number;
}

let p: Point = { x: 1, y: 2 };

// Function subtyping via type alias
type NumberFn = (x: number) => number;
function makeDouble(x: number): number {
  return x * 2;
}
let double: NumberFn = makeDouble;

console.log(a);
console.log(b);
console.log(double(21));
