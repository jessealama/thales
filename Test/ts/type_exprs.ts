// Test function types
type Fn = (x: number) => string;
type NoArgs = () => boolean;
type RestFn = (...args: number) => void;
type OptFn = (name: string, age?: number) => void;

// Test tuple types
type Pair = [string, number];
type Triple = [number, number, number];

// Test object literal types
type Point = { x: number; y: string };
type Opt = { name: string; age?: number };
type Ro = { readonly id: number };

console.log('type_exprs OK');
