const xs = [1, 2, 3];
const doubledSum = xs.map((x) => x * 2).reduce((a, b) => a + b, 0);
console.log(doubledSum);
