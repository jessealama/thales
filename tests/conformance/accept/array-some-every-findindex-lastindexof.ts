// Read-only Array methods: some/every/findIndex (predicate) and
// lastIndexOf (search from the end, optional fromIndex).
const xs: number[] = [3, 1, 2];
console.log(xs.some((x) => x > 1)); // true
console.log(xs.every((x) => x > 1)); // false
console.log(xs.every((x) => x > 0)); // true
console.log(xs.findIndex((x) => x > 1)); // 0
console.log(xs.findIndex((x) => x > 5)); // -1

const rep: number[] = [1, 2, 1, 2];
console.log(rep.findIndex((x) => x === 2)); // 1
console.log(rep.lastIndexOf(1)); // 2
console.log(rep.lastIndexOf(2)); // 3
console.log(rep.lastIndexOf(9)); // -1
console.log(rep.lastIndexOf(1, 1)); // 0
console.log(rep.lastIndexOf(2, -1)); // 3
console.log(rep.lastIndexOf(2, -3)); // 1
console.log(rep.lastIndexOf(2, -5)); // -1

const ss: string[] = ['a', 'b', 'c', 'b'];
console.log(ss.some((s) => s === 'c')); // true
console.log(ss.findIndex((s) => s === 'b')); // 1
console.log(ss.lastIndexOf('b')); // 3
console.log(ss.lastIndexOf('b', 2)); // 1
console.log(ss.lastIndexOf('z')); // -1
