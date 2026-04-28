// Subset-rejected example: a `@total` function whose body contains an
// uncaught `throw` (TH0067). `@total` requires that no failure escapes
// the function. Either catch the throw with try/catch, or annotate the
// function with `@throws` instead.

/** @total */
function abs(n: number): number {
  if (n < 0) {
    // @thales-expect-error TH0067
    throw new RangeError("negative");
  }
  return n;
}

console.log(abs(3));
