// Tightening behavior change: a `try` block with only `finally`
// (no `catch`) does not consume throws — they pass through. Calling a
// @throws function inside try-finally without declaring @throws on the
// caller now fires TH0060.

/** @throws RangeError */
function risky(): number {
  throw new RangeError('nope');
}

function withCleanup(): number {
  try {
    // @thales-expect-error TH0060
    return risky();
  } finally {
    // cleanup runs but does not catch
  }
}

console.log(withCleanup());
