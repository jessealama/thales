// Contextual typing error tests — these should produce type errors

// Wrong type in object literal property
interface Point {
  x: number;
  y: number;
}

let badPoint: Point = { x: "hello", y: 2 };

// Wrong type in array literal element
let badNums: number[] = [1, "two", 3];
