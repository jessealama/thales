// Loosening behavior change: a `throw` inside a `try` block whose
// `catch` consumes it does NOT require `@throws` on the enclosing
// function. Today this fires TH0060 syntactically from SubsetCheck;
// after Task 5 the syntactic path is removed and Check.lean correctly
// classifies the throw as caught.
//
// The emitter only desugars try/catch when the body is a call to a
// `@throws` function (return-shape or const-binding shape), so this
// fixture uses that shape rather than a bare `throw`. The `@throws`
// callee plays the role of "throws something the catch consumes."

/** @throws RangeError */
function risky(): number {
  throw new RangeError('retry');
}

function safeAttempt(): number {
  try {
    return risky();
  } catch (e) {
    return 0;
  }
}

console.log(safeAttempt());
