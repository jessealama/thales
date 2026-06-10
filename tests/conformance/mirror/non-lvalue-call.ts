// Mirror: tsc emits TS2364 for a call-result LHS.
function f(): number {
  return 0;
}
f() = 1;
