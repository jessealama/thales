// Strict-TS port of test262's harness/assert.js. The function + namespace
// merge gives the callable-with-properties shape of the upstream `assert`
// object. Message strings are byte-identical to upstream where reachable.
// `assert.compareArray` and `isPrimitive` are not ported: slice tests that
// compare arrays declare `includes: [compareArray.js]`, which the runner
// skips as an unported include.

function isNegativeZero(value: unknown): boolean {
  return value === 0 && 1 / value === -Infinity;
}

function formatIdentityFreeValue(value: unknown): string | undefined {
  switch (value === null ? 'null' : typeof value) {
    case 'string':
      return JSON.stringify(value);
    case 'bigint':
      return String(value) + 'n';
    case 'number':
      // Upstream falls through to String(value) after the -0 special
      // case; spelled out because noFallthroughCasesInSwitch forbids it.
      if (isNegativeZero(value)) return '-0';
      return String(value);
    case 'boolean':
    case 'undefined':
    case 'null':
      return String(value);
    default:
      return undefined;
  }
}

function formatSimpleValue(value: unknown): string {
  const basic = formatIdentityFreeValue(value);
  if (basic) return basic;
  try {
    return String(value);
  } catch (err) {
    if (err instanceof Error && err.name === 'TypeError') {
      return Object.prototype.toString.call(value);
    }
    throw err;
  }
}

/** @throws Test262Error */
function assert(mustBeTrue: unknown, message?: string): void {
  if (mustBeTrue === true) {
    return;
  }

  if (message === undefined) {
    message = 'Expected true but got ' + assert._toString(mustBeTrue);
  }
  throw new Test262Error(message);
}

namespace assert {
  export function _isSameValue(a: unknown, b: unknown): boolean {
    // Upstream hand-rolls the SameValue algorithm for pre-ES6 engines;
    // Object.is is that algorithm.
    return Object.is(a, b);
  }

  export const _formatIdentityFreeValue = formatIdentityFreeValue;
  export const _toString = formatSimpleValue;

  /** @throws Test262Error */
  export function sameValue(
    actual: unknown,
    expected: unknown,
    message?: string,
  ): void {
    try {
      if (_isSameValue(actual, expected)) {
        return;
      }
    } catch (error) {
      // String(message) preserves upstream's "undefined ..." output when
      // no message was given (upstream concatenates the raw parameter).
      throw new Test262Error(
        String(message) + ' (_isSameValue operation threw) ' + String(error),
      );
    }

    if (message === undefined) {
      message = '';
    } else {
      message += ' ';
    }

    message +=
      'Expected SameValue(«' +
      _toString(actual) +
      '», «' +
      _toString(expected) +
      '») to be true';

    throw new Test262Error(message);
  }

  /** @throws Test262Error */
  export function notSameValue(
    actual: unknown,
    unexpected: unknown,
    message?: string,
  ): void {
    if (!_isSameValue(actual, unexpected)) {
      return;
    }

    if (message === undefined) {
      message = '';
    } else {
      message += ' ';
    }

    message +=
      'Expected SameValue(«' +
      _toString(actual) +
      '», «' +
      _toString(unexpected) +
      '») to be false';

    throw new Test262Error(message);
  }

  /** @throws Test262Error */
  export function throws(
    expectedErrorConstructor: new (...args: never[]) => Error,
    func: () => unknown,
    message?: string,
  ): void {
    if (typeof func !== 'function') {
      throw new Test262Error(
        'assert.throws requires two arguments: the error constructor ' +
          'and a function to run',
      );
    }
    if (message === undefined) {
      message = '';
    } else {
      message += ' ';
    }

    try {
      func();
    } catch (thrown) {
      if (typeof thrown !== 'object' || thrown === null) {
        message += 'Thrown value was not an object!';
        throw new Test262Error(message);
      } else if (thrown.constructor !== expectedErrorConstructor) {
        const expectedName = expectedErrorConstructor.name;
        const actualName = thrown.constructor.name;
        if (expectedName === actualName) {
          message +=
            'Expected a ' +
            expectedName +
            ' but got a different error constructor with the same name';
        } else {
          message += 'Expected a ' + expectedName + ' but got a ' + actualName;
        }
        throw new Test262Error(message);
      }
      return;
    }

    message +=
      'Expected a ' +
      expectedErrorConstructor.name +
      ' to be thrown but no exception was thrown at all';
    throw new Test262Error(message);
  }
}
