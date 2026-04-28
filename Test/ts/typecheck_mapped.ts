// Mapped type tests — this file should type-check cleanly
// All test cases validated against tsc --noEmit --strict

interface Point {
  x: number;
  y: number;
}

// Basic mapped type: identity
type Identity<T> = { [K in keyof T]: T[K] };
let p1: Identity<Point> = { x: 1, y: 2 };

// Partial: add optional modifier
type MyPartial<T> = { [K in keyof T]?: T[K] };
let p2: MyPartial<Point> = { x: 1 };
let p3: MyPartial<Point> = {};

// Readonly
type MyReadonly<T> = { readonly [K in keyof T]: T[K] };
let p4: MyReadonly<Point> = { x: 1, y: 2 };

// Record: explicit key set
type MyRecord<K extends string, V> = { [P in K]: V };
type RGB = MyRecord<"r" | "g" | "b", number>;
let rgb: RGB = { r: 255, g: 128, b: 0 };

// Pick: subset of keys
type MyPick<T, K extends keyof T> = { [P in K]: T[P] };
type XOnly = MyPick<Point, "x">;
let xo: XOnly = { x: 42 };

// Required: remove optional modifier
interface Config {
  host: string;
  port?: number;
}
type MyRequired<T> = { [K in keyof T]-?: T[K] };
let cfg: MyRequired<Config> = { host: "localhost", port: 8080 };

console.log(p1, p2, p3, p4, rgb, xo, cfg);
