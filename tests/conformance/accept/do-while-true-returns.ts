// A `do … while (true)` that returns on every interior path never completes,
// just like `while (true)`. But it lowers to a different Lean construct, and a
// trailing `return ()`/`unreachable!` appended after a `repeat … until` is
// rejected ("must be last element in a `do` sequence"). The emitter must lower
// the constant-`true` guard to `while true do …` so the unreachable tail is
// legal (issue #72; sibling of #64's `while (true)` fix).
function g(n: number): number {
  do {
    if (n > 0) {
      return n;
    }
    return 0;
  } while (true);
}

console.log(g(7));
console.log(g(-2));
