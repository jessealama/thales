// Subset-rejected example: undiscriminated primitive union (TH0022).
// @thales-expect-error TH0022
function double(x: string | number): string | number {
  if (typeof x === "number") return x * 2;
  return x + x;
}
console.log(double(21));
