// Subset-rejected example: a block-scoped declaration shadowing an
// enclosing binding (TH0032). tsc accepts; thales rejects because the
// emitter flattens bare blocks, so the inner `n` would capture the
// `return n` reference meant for the outer binding (#45).
function f(): number {
  const n = 0;
  {
    // @thales-expect-error TH0032
    const n = 1;
  }
  return n;
}
console.log(f());
