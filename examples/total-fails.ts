/** @total */
// @thales-expect-error TH0070
function fact(n: bigint): bigint {
  if (n === 0n) return 1n;
  return n * fact(n - 1n);
}

console.log(fact(5n));
