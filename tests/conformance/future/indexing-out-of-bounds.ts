// Out-of-bounds literal index stays optional — Thales does not lift arr[5]
// when the array only has 3 elements.
const arr = [10, 20, 30];
const maybe = arr[5]; // stays number | undefined (5 >= 3)
if (maybe !== undefined) {
  console.log(maybe);
} else {
  console.log('out of bounds');
}
