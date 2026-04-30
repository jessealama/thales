function f2(cond: boolean) {
  let x: string;
  if (cond) {
    x = 'hello';
  }
  x;
}

function f1(cond: boolean) {
  let x: string;
  if (cond) {
    x = 'hello';
  } else {
    x = 'world';
  }
  x;
}
