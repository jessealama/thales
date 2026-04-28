// Subset-rejected example: non-exhaustive switch on discriminated union (TH0040).
type Shape = { kind: "circle"; r: number } | { kind: "square"; side: number };
function describe(s: Shape) {
  // @thales-expect-error TH0040
  switch (s.kind) {
    case "circle": console.log("circle r=" + s.r); break;
    // missing "square" case
  }
}
describe({ kind: "circle", r: 3 });
