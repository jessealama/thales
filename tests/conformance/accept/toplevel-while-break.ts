// Top-level while with break/continue (issue #49): prints 0,1,2.
let i = 0;
while (true) {
  if (i >= 3) {
    break;
  }
  console.log(i);
  i = i + 1;
}
