type Shape =
  | { kind: "circle"; r: number }
  | { kind: "square"; s: number };

function area(shape: Shape): number {
  switch (shape.kind) {
    case "circle": return 3.14 * shape.r * shape.r;
    case "square": return shape.s * shape.s;
  }
}

const main = (): number => area({ kind: "circle", r: 2 });
console.log(main());
