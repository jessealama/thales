// Array element reads are `T | undefined` (noUncheckedIndexedAccess):
// bind-then-narrow is the sanctioned pattern. Out-of-bounds, fractional,
// negative, and absurdly large indices all read as `undefined`, exactly
// as in JS.
const words: string[] = ['zero', 'one', 'two'];

function wordAt(i: number): string {
  const hit = words[i];
  if (hit !== undefined) {
    return hit;
  }
  return 'missing';
}

console.log(wordAt(0));
console.log(wordAt(2));
console.log(wordAt(3));
console.log(wordAt(-1));
console.log(wordAt(0.5));
console.log(wordAt(1e99));
