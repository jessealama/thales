// Conditional type error tests — these should produce type errors

// Exclude resolves to number | boolean, so string shouldn't be assignable
type MyExclude<T, U> = T extends U ? never : T;
type ExResult = MyExclude<string | number | boolean, string>;
let bad1: ExResult = "hello";

// ReturnType resolves to string, so number shouldn't be assignable
type MyReturnType<T> = T extends (...args: any[]) => infer R ? R : never;
type RT = MyReturnType<() => string>;
let bad2: RT = 42;

// ElementType resolves to string, so number shouldn't be assignable
type ElementType<T> = T extends Array<infer U> ? U : never;
type Elem = ElementType<string[]>;
let bad3: Elem = 42;
