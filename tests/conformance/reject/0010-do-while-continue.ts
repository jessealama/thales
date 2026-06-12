// Subset-rejected example: do-while whose body has a loop-level `continue`
// (TH0010). TS `continue` in a do-while jumps to the test; Lean's
// `repeat ... until` re-enters the body without checking, so the lowering
// would diverge where TS exits. The shape stays rejected.
function f(n: number): number {
  // @thales-expect-error TH0010
  do {
    if (n > 0) {
      continue;
    }
  } while (n > 0);
  return n;
}
console.log(f(0));
