// A const local bound to a `T | undefined`-returning call narrows with
// `!== undefined`, reading at the unwrapped type in the narrowed branch
// (the local-variable counterpart of nullable-negated-test.ts's parameter
// narrowing).
function pick(b: boolean): string | undefined {
  if (b) {
    return 'yes';
  }
  return undefined;
}

function describe(b: boolean): string {
  const hit = pick(b);
  if (hit !== undefined) {
    return hit + '!';
  }
  return 'none';
}

console.log(describe(true));
console.log(describe(false));
