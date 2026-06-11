// #24: branching + early return with mutation. The no-else `if` keeps its
// mutation visible after the branch; the early return is do-notation's
// native `return`.
function classify(score: number): number {
  let bonus = 0;
  if (score < 0) {
    return -1;
  }
  if (score > 50) {
    bonus += 10;
  } else {
    bonus += 1;
  }
  bonus += score;
  return bonus;
}
console.log(classify(-5));
console.log(classify(60));
console.log(classify(10));
