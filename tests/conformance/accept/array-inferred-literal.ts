// number[]/string[] inferred from a homogeneous array literal (or from a
// function's return type) lower the same as an explicitly annotated receiver.
const xs = [3, 1, 2];
console.log(xs.join(','));
console.log(xs.indexOf(2));
console.log(xs.includes(3));

const ss = ['a', 'b'];
console.log(ss.join('-'));

function getArr(): number[] {
  return [3, 1, 2];
}
const ys = getArr();
console.log(ys.join('/'));
