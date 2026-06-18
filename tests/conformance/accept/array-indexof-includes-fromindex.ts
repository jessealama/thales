// #67: indexOf/includes accept an optional `fromIndex` second argument.
const xs: number[] = [1, 2, 1, 2];
console.log(xs.indexOf(2, 1)); // 1
console.log(xs.indexOf(1, 1)); // 2
console.log(xs.indexOf(2, -1)); // 3
console.log(xs.indexOf(1, -2)); // 2
console.log(xs.indexOf(1, -100)); // 0
console.log(xs.indexOf(2, 5)); // -1
console.log(xs.indexOf(2, 1.9)); // 1 (fromIndex truncates toward zero)
console.log(xs.includes(2, 1)); // true
console.log(xs.includes(1, -2)); // true
console.log(xs.includes(2, 5)); // false

const ss: string[] = ['a', 'b', 'c'];
console.log(ss.indexOf('c', 1)); // 2
console.log(ss.indexOf('a', 1)); // -1
console.log(ss.includes('a', 1)); // false
console.log(ss.includes('c', -1)); // true
