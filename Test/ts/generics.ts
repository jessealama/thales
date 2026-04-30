function first<T>(arr: T[]): T {
  return arr[0];
}

interface Container<T> {
  value: T;
}

type Result<T, E> = T | E;

console.log(first([10, 20, 30]));
console.log(first(['a', 'b', 'c']));
