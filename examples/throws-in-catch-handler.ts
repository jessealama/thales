// A function annotated @throws whose catch handler throws an error of
// the declared type. Compiles cleanly: the catch handler's throw is an
// uncaught throw event under the propagation rule, but the enclosing
// function carries @throws so TH0060 does not fire.

/** @throws RangeError */
function tryParseOrFail(s: string): number {
  try {
    if (s === "") throw new RangeError("empty");
    return parseFloat(s);
  } catch (e) {
    throw new RangeError("rethrown");
  }
}

console.log(tryParseOrFail("42"));
