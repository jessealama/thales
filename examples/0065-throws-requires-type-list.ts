// Subset-rejected: `@throws` with no type list is not yet supported
// (v1 requires at least one type). Track follow-up: body-inference of
// throw types when the user omits the list.

/** @throws */
// @thales-expect-error TH0065
function maybeThrows(): number {
  throw new RangeError('oops');
}

console.log(maybeThrows());
