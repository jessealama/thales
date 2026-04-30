// Mapped type error tests — these should produce type errors

interface Point {
  x: number;
  y: number;
}

// Wrong value type in Partial property
type MyPartial<T> = { [K in keyof T]?: T[K] };
let bad1: MyPartial<Point> = { x: 'hello' };

// Wrong value type in Record
type MyRecord<K extends string, V> = { [P in K]: V };
type RGB = MyRecord<'r' | 'g' | 'b', number>;
let bad2: RGB = { r: 255, g: 'oops', b: 0 };
