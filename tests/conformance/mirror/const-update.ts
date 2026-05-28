// Mirror: tsc emits TS2588 for ++/-- on a const-declared binding.
const x = 1;
x++;
--x;
