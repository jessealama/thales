function identity<T>(x: T): T {
  return x;
}
let bad1: number = identity<string>('hello');

interface Point {
  x: number;
  y: number;
}
type PointKeys = keyof Point;
let bad2: PointKeys = 'z';

type PointX = Point['x'];
let bad3: PointX = 'hello';

enum Color {
  Red,
  Green,
  Blue,
}
let bad4: Color = 999;
let bad5: Color = 'Red';
