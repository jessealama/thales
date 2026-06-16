// Subset-rejected example: arithmetic on a possibly-undefined value (TH0082).
// `xs[i]` is `T | undefined` under noUncheckedIndexedAccess; tsc accepts
// `(string | undefined) + string`, but the subset requires narrowing first:
// bind the read (`const hit = xs[i]`) and test `hit !== undefined`.
const greetings: string[] = ['hi', 'hello'];
function greet(i: number, name: string): string {
  // @thales-expect-error TH0082
  return greetings[i] + ' ' + name;
}
console.log(greet(0, 'world'));
