// `while (true)` that returns on every interior path never completes, so tsc
// requires no return after it. The emitter must not append a trailing
// `return ()` at the function's (non-unit) return type.
function f(n: number): number {
  while (true) {
    if (n > 0) {
      return n;
    }
    return 0;
  }
}

console.log(f(5));
console.log(f(-3));
