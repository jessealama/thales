// Element read inside a do-mode body (let-mutation + while): the Float
// loop counter feeds indexRead directly (#52's untested combination), and
// the narrowed early return exits the loop from inside the match arm.
const digits: string[] = ['a', 'b', 'c', 'd'];

function nthOrGone(n: number): string {
  let i = 0;
  while (i < 10) {
    const hit = digits[i + n];
    if (hit !== undefined) {
      return hit;
    }
    if (n <= i) {
      return 'gone';
    }
    i = i + 1;
  }
  return 'never';
}

console.log(nthOrGone(0));
console.log(nthOrGone(3));
console.log(nthOrGone(9));
