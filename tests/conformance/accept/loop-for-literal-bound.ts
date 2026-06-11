// #25: canonical C-style for with an integer-literal bound lowers to a
// Lean range loop; the Nat binder is shimmed back to Float for body uses.
function sumBelow(): number {
  let total = 0;
  for (let i = 0; i < 5; i++) {
    total += i;
  }
  return total;
}
console.log(sumBelow());
