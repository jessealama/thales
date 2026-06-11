// Subset-rejected example: mutating a variable captured by a closure (TH0005).
// tsc accepts; thales rejects because Lean's `let mut` cannot be captured —
// a binding is mutable only if no nested function/arrow references it.
function f(): number {
  let n = 0;
  const bump = () => {
    // @thales-expect-error TH0005
    n = n + 1;
  };
  bump();
  return n;
}
console.log(f());
