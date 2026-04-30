interface A {
  a: string;
}
interface B {
  b: number;
}

function test<T extends A & B>(x: T) {
  let a: string = x.a;
  let b: number = x.b;
}
