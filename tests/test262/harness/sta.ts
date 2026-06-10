// Strict-TS port of test262's harness/sta.js (implicitly included in every
// non-raw test). Same global names, same observable behavior on the API
// surface the slices exercise. Upstream corners the slices don't use
// (`Test262Error(msg)` without `new`, `Test262Error.thrower`) are
// deliberately not reproduced: a test relying on them surfaces as a type
// error and classifies as out-of-subset, never a silent divergence.

class Test262Error extends Error {
  constructor(message: string = '') {
    super(message);
    this.name = 'Test262Error';
  }

  // Upstream prints "Test262Error: <message>" even when the message is
  // empty (Error.prototype.toString would drop the ": ").
  override toString(): string {
    return 'Test262Error: ' + this.message;
  }
}

function $DONOTEVALUATE(): never {
  // Upstream throws a bare string, not an Error — preserved verbatim.
  // Only reachable from `negative` tests, which the runner skips.
  throw 'Test262: This statement should not be evaluated.';
}
