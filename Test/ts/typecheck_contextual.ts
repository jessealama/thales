// Contextual typing tests — this file should type-check cleanly

// Array contextual typing: expected element type flows into array literal
let nums: number[] = [1, 2, 3];
let strs: string[] = ['a', 'b', 'c'];

console.log(nums);
console.log(strs);

// Object contextual typing: expected member types flow into object literal properties
interface Point {
  x: number;
  y: number;
}

let p: Point = { x: 1, y: 2 };

interface Named {
  name: string;
  age: number;
}

let person: Named = { name: 'Alice', age: 30 };
console.log(p);
console.log(person);
