// #26: `do`/`while` lowers to Lean `repeat ... until !(test)`. The body
// must run once even when the test is false on entry.
function countdownSteps(n: number): number {
  let steps = 0;
  do {
    steps += 1;
    n -= 1;
  } while (n > 0);
  return steps;
}
console.log(countdownSteps(3));
console.log(countdownSteps(-5));
