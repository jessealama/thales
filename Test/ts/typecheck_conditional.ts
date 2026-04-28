// Conditional type tests — this file should type-check cleanly
// All test cases validated against tsc --noEmit --strict

// Basic conditional type
type IsString<T> = T extends string ? true : false;
let a: IsString<string> = true;
let b: IsString<number> = false;

// Distributive conditional: Exclude
type MyExclude<T, U> = T extends U ? never : T;
type ExResult = MyExclude<string | number | boolean, string>;
let c: ExResult = 42;
let d: ExResult = true;

// Distributive conditional: Extract
type MyExtract<T, U> = T extends U ? T : never;
type ExtResult = MyExtract<string | number | boolean, string | boolean>;
let e: ExtResult = "hello";
let f: ExtResult = true;

// infer: return type extraction
type MyReturnType<T> = T extends (...args: any[]) => infer R ? R : never;
type RT1 = MyReturnType<() => string>;
let g: RT1 = "hello";

type RT2 = MyReturnType<(x: number) => boolean>;
let h: RT2 = true;

// infer: array element type
type ElementType<T> = T extends Array<infer U> ? U : never;
type Elem1 = ElementType<string[]>;
let i: Elem1 = "test";

// Non-distribution: wrapped type param
type NoDistribute<T> = [T] extends [string] ? "yes" : "no";
type ND1 = NoDistribute<string>;
type ND2 = NoDistribute<string | number>;
let j: ND1 = "yes";
let k: ND2 = "no";

// NonNullable via conditional
type MyNonNullable<T> = T extends null | undefined ? never : T;
type NN1 = MyNonNullable<string | null | undefined>;
let l: NN1 = "hello";

console.log(a, b, c, d, e, f, g, h, i, j, k, l);
