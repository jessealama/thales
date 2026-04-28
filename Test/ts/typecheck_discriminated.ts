// Discriminated union and switch narrowing tests — should type-check cleanly
// All test cases validated against tsc --noEmit --strict

// Discriminated union type
type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "rect"; width: number; height: number };

// Narrowing with if/else
function area(s: Shape): number {
  if (s.kind === "circle") {
    return 3.14 * s.radius * s.radius;
  } else {
    return s.width * s.height;
  }
}

// Narrowing with switch
function describe(s: Shape): string {
  switch (s.kind) {
    case "circle":
      return "circle with radius " + s.radius;
    case "rect":
      return "rect " + s.width + "x" + s.height;
  }
  return "unknown";
}

// typeof switch
function typeSwitch(x: string | number | boolean): string {
  switch (typeof x) {
    case "string":
      let s: string = x;
      return s;
    case "number":
      let n: number = x;
      return "num";
    case "boolean":
      let b: boolean = x;
      return "bool";
  }
  return "other";
}

// Negated discriminant: !== in if
function notCircle(s: Shape): void {
  if (s.kind !== "circle") {
    console.log(s.width);
  }
}

console.log(area({ kind: "circle", radius: 5 }));
console.log(area({ kind: "rect", width: 3, height: 4 }));
console.log(describe({ kind: "circle", radius: 5 }));
console.log(typeSwitch("hello"));
notCircle({ kind: "rect", width: 1, height: 2 });
