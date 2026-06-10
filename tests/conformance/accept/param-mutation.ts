// #24: parameter mutation. JS parameters are mutable locals whose
// mutation never affects the caller; emitted via self-shadowing
// (`let mut x := x`).
function clampToTen(x: number): number {
  x = x > 10 ? 10 : x;
  x += 1;
  return x;
}
console.log(clampToTen(20));
console.log(clampToTen(3));
