// #44: a `default` arm on a discriminated-union switch lowers as the
// wildcard match arm (it used to render `unreachable!` — a runtime panic
// on any constructor not covered by a `case`).
type Shape = { kind: 'circle'; r: number } | { kind: 'square'; s: number };

function area(shape: Shape): number {
  switch (shape.kind) {
    case 'circle':
      return 3 * shape.r * shape.r;
    default:
      return 0;
  }
}

console.log(area({ kind: 'circle', r: 2 }));
console.log(area({ kind: 'square', s: 4 }));
