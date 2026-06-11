// #24: discriminated-union switch inside a do-mode body. Every arm
// returns (do-mode's v1 switch shape), and the arms mutate a local.
type Shape = { kind: 'circle'; r: number } | { kind: 'square'; s: number };

function scaledArea(shape: Shape): number {
  let area = 0;
  switch (shape.kind) {
    case 'circle':
      area = 3 * shape.r * shape.r;
      area += 1;
      return area;
    case 'square':
      area = shape.s * shape.s;
      return area;
  }
}

console.log(scaledArea({ kind: 'circle', r: 2 }));
console.log(scaledArea({ kind: 'square', s: 4 }));
