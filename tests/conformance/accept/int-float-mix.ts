function addBig(a: bigint, b: bigint): bigint {
  return a + b;
}

function scaleFloat(x: number): number {
  return x * 2;
}

const main = (): bigint => addBig(10n, 5n);
console.log(main());
console.log(scaleFloat(3.14));
