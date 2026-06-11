// #43: a negated null test lowers to an Option match with swapped arms,
// so the branch reads the variable at its narrowed (unwrapped) type.
function len(x: string | null): number {
  if (x !== null) {
    return x.length;
  }
  return -1;
}
console.log(len('abc'));
console.log(len(null));
