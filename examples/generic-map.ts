function pair<A, B>(a: A, b: B): A {
  return a;
}

const main = (): number => pair<number, boolean>(42, true);
console.log(main());
