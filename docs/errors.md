# Thales-TS Error Code Reference

## Error code alignment

Every thales diagnostic either:

- uses a `TSXXXX` code that tsc would also emit at the same
  line for the same input
- uses a `TH####` code, listed below, for subset-specific
  violations. These codes have no tsc equivalent and exist
  only because thales is stricter than tsc about what
  programs it is willing to embed into Lean.

Extra `TH####` diagnostics never cause a conformance failure. A `TSXXXX`
diagnostic reported by thales that tsc would not produce is a bug; report it.
Column positions are not currently compared by the conformance harness
because thales and tsc disagree on per-diagnostic anchoring, but they are
displayed in diagnostics for human readability.

See `docs/superpowers/specs/2026-04-21-conformance-harness-design.md` for
the full contract and harness details.

This reference lists all 20 subset `TH####` codes plus the 5 directive
codes (TH9000–TH9004) with minimal detail. For full explanation,
rationale, and idiomatic replacements, see [subset.md](./subset.md).

The codes are divided into categories:

- mutation
- control flow
- types
- declarations
- recursion
- totality
- exceptions
- refinement types

Another category, directives, exists for meta purposes
(doesn't correspond to a real subset of TypeScript but
rather reflects a kind of misuse of Thales or an emit-pipeline
soundness check).

## Summary

| Code   | Category     | Short Message                                       |
| ------ | ------------ | --------------------------------------------------- |
| TH0001 | Mutation     | Cannot reassign variable                            |
| TH0002 | Mutation     | Cannot assign to array element                      |
| TH0003 | Mutation     | Cannot assign to object property                    |
| TH0004 | Mutation     | Cannot call mutating method                         |
| TH0005 | Mutation     | Cannot mutate variable captured by enclosing scope  |
| TH0006 | Mutation     | Assignment only supported in statement position     |
| TH0007 | Mutation     | Cannot mutate inside `@throws` or `try`/`catch`     |
| TH0010 | Control flow | Loop not supported                                  |
| TH0012 | Control flow | async/await not supported                           |
| TH0020 | Types        | `any` not permitted                                 |
| TH0021 | Types        | `unknown` not permitted in user code                |
| TH0022 | Types        | Union must be discriminated                         |
| TH0023 | Types        | Intersection types not supported                    |
| TH0024 | Types        | keyof/conditional/mapped types not supported        |
| TH0025 | Types        | null/undefined types not supported                  |
| TH0030 | Declarations | `class` not supported                               |
| TH0031 | Declarations | Inheritance (`extends`) not supported               |
| TH0040 | Matching     | Non-exhaustive switch on discriminated union        |
| TH0050 | Recursion    | Cannot verify termination                           |
| TH0066 | Totality     | `@total` and `@throws` declared together            |
| TH0067 | Totality     | `@total` function has uncaught throw                |
| TH0070 | Totality     | `@total` asserted but Lean rejects termination      |
| TH0060 | Exceptions   | Unannotated `throw`                                 |
| TH0061 | Exceptions   | Unused `@throws` annotation                         |
| TH0063 | Exceptions   | Thrown value must be a record type                  |
| TH0064 | Exceptions   | Undeclared propagation                              |
| TH0080 | Refinement   | Literal value out of range for refinement type      |
| TH0081 | Refinement   | Value not assignable to refinement without evidence |
| TH9000 | Directive    | Unused `@thales-expect-error` directive             |
| TH9001 | Directive    | Directive code mismatch                             |
| TH9002 | Directive    | Cannot emit: subset violations suppressed           |
| TH9003 | Directive    | Malformed `@thales-expect-error` directive          |
| TH9004 | Directive    | Emitted Lean code contains `sorry`                  |

## Future of this table

As Thales develops, some of the diagnostic codes might
become obsolete. That is, they will never be emitted. This
is because the subset of TypeScript that we intend to target
will grow over time.

## Mutation

### TH0001 — Cannot reassign variable

**Message:** `Cannot reassign variable`

Since #24, function-local non-escaping mutation is **in subset** (emitted
as `Id.run do` with `let mut`). TH0001 now covers only the still-rejected
forms:

- module-level reassignment: `let x = 0; x = 1;` at the top level;
- logical assignment operators (`&&=`, `||=`, `??=`);
- reassignment of a `let` declared without an initializer
  (`let x: number; x = 1;` — give it an initializer instead);
- reassignment of a variable whose narrowing the emitter relies on
  (null-tested or refinement-predicate-tested in a condition).

[Details in subset.md#th0001--cannot-reassign-variable](./subset.md#th0001--cannot-reassign-variable)

---

### TH0002 — Cannot assign to array element

**Message:** `Cannot assign to array element; use \`.concat\` or return a new array`

Rejected: `arr[0] = 99;`

[Details in subset.md#th0002--cannot-assign-to-array-element-use-concat-or-return-a-new-array](./subset.md#th0002--cannot-assign-to-array-element-use-concat-or-return-a-new-array)

---

### TH0003 — Cannot assign to object property

**Message:** `Cannot assign to object property; construct a new object`

Rejected: `obj.x = 10;`

[Details in subset.md#th0003--cannot-assign-to-object-property-construct-a-new-object](./subset.md#th0003--cannot-assign-to-object-property-construct-a-new-object)

---

### TH0004 — Cannot call mutating method

**Message:** `Cannot call mutating method`

Rejected: `arr.push(42);`

[Details in subset.md#th0004--cannot-call-mutating-method](./subset.md#th0004--cannot-call-mutating-method)

---

### TH0005 — Cannot mutate variable captured by enclosing scope

**Message:** `Cannot mutate variable captured by enclosing scope`

Rejected: `let sum = 0; arr.forEach(x => { sum += x; });`

A binding is mutable only when every reference to it (read _or_ write)
occurs in the declaring function's own body. JS closures capture the live
binding; Lean's `let mut` cannot be captured at all, and a read-only
capture of a mutated variable would silently snapshot the value. Mutating
a variable declared in an enclosing scope, or mutating a variable that any
nested function/arrow mentions, is rejected. Workaround: restructure so
the nested function takes the value as a parameter or returns the update.

[Details in subset.md#th0005--cannot-mutate-variable-captured-by-enclosing-scope](./subset.md#th0005--cannot-mutate-variable-captured-by-enclosing-scope)

---

### TH0006 — Assignment only supported in statement position

**Message:** `Assignment and update expressions are only supported as statements; assign in a separate statement`

Rejected: `const y = (n = 1);`, `f(n += 1)`, `return n++;`

Assignment and update expressions produce values in JavaScript, but the
Thales subset treats mutation as a statement-level effect. Split the
mutation into its own statement:

```ts
n++;
return n - 1; // instead of `return n++;`
```

---

### TH0007 — Cannot mutate inside `@throws` or `try`/`catch`

**Message:** `Cannot mutate variable inside a \`@throws\` function or \`try\`/\`catch\``

Rejected: mutation in the body of a `@throws`-annotated function, or
anywhere under a `try`/`catch`.

The `@throws` path emits pure `Except` match-chains; the mutation path
emits `Id.run do` blocks. Unifying them is staged as a follow-up, mirroring
how `@throws`/`@total` exclusivity was staged. Workaround: hoist the
mutation into a helper function without `@throws`, or compute the value
purely.

---

## Control flow

### TH0010 — Loop not supported

**Message:** `Loop not supported; use recursion or array methods`

Rejected: `for (let i = 0; i < n; i++) { ... }`

[Details in subset.md#th0010--loop-not-supported-use-recursion-or-array-methods](./subset.md#th0010--loop-not-supported-use-recursion-or-array-methods)

---

### TH0011 — throw/try/catch not supported

**Status:** Partially lifted. `throw new E(msg)` inside a `@throws`-annotated function is now
accepted and emitted as `Except.error`. `try/catch` blocks are also accepted (the catch type
is inferred from the called function's `@throws` annotation). TH0011 still fires for `throw`
outside an annotated function (use TH0060 instead) — see TH0060.

**Remaining restrictions:** No `finally` clause. No multi-catch. No rethrow.

[Details in subset.md](./subset.md#throws-and-exception-handling)

---

### TH0012 — async/await not supported

**Message:** `\`async\`/\`await\` not supported`

Rejected: `async function f() { await fetch(...); }`

[Details in subset.md#th0012--asyncawait-not-supported](./subset.md#th0012--asyncawait-not-supported)

6+ integrates async orchestration with `IO` monad.

---

## Types

### TH0020 — any not permitted

**Message:** `\`any\` is not permitted`

Rejected: `function f(x: any): any { return x; }`

[Details in subset.md#th0020--any-is-not-permitted](./subset.md#th0020--any-is-not-permitted)

Permanent — use generics (`<T>`) instead.

---

### TH0021 — unknown not permitted

**Message:** `\`unknown\` is not permitted in user code`

Rejected: `function f(x: unknown): string { return String(x); }`

[Details in subset.md#th0021--unknown-is-not-permitted-in-user-code](./subset.md#th0021--unknown-is-not-permitted-in-user-code)

3 adds `Result<T, E>` for controlled narrowing in JSON parsing.

---

### TH0022 — Union must be discriminated

**Message:** `Union must be discriminated`

Rejected: `type T = string | number; function f(x: T) { ... }`

[Details in subset.md#th0022--union-must-be-discriminated](./subset.md#th0022--union-must-be-discriminated)

Permanent — use discriminated unions with a `kind` tag.

---

### TH0023 — Intersection types not supported

**Message:** `Intersection types are not supported`

Rejected: `type T = A & B;`

[Details in subset.md#th0023--intersection-types-are-not-supported](./subset.md#th0023--intersection-types-are-not-supported)

Permanent — flatten to a single `interface`.

---

### TH0024 — keyof/conditional/mapped types not supported

**Message:** `\`keyof\`/conditional/mapped types are not supported`

Rejected: `type Keys = keyof T; type Readonly<T> = { readonly [K in keyof T]: T[K] };`

[Details in subset.md#th0024--keyofconditionalmapped-types-are-not-supported](./subset.md#th0024--keyofconditionalmapped-types-are-not-supported)

Permanent — out of shallow-embedding scope.

---

### TH0025 — null/undefined types not supported

**Status:** Lifted. `T | null` and `T | undefined` are now accepted and
emitted as `Option T`. This code is no longer emitted by `thales`.

Historical message: `null/undefined types not supported; use Option<T>`

If you have a `@thales-expect-error TH0025` directive in your source, remove
it — the directive is now unused and will produce TH9000.

See `docs/subset.md` (Nullable types section) for the full translation rules.

---

## Declarations

### TH0030 — class not supported

**Message:** `\`class\` not supported`

Rejected: `class Counter { count = 0; increment() { this.count++; } }`

[Details in subset.md#th0030--class-not-supported](./subset.md#th0030--class-not-supported)

2 adds classes via `structure` + `namespace` desugaring.

---

### TH0031 — Inheritance not supported

**Message:** `Inheritance (\`extends\`) not supported`

Rejected: `class Dog extends Animal { ... }`

[Details in subset.md#th0031--inheritance-extends-not-supported](./subset.md#th0031--inheritance-extends-not-supported)

6+ adds single-dispatch inheritance via typeclasses.

---

## Matching

### TH0040 — Non-exhaustive switch

**Message:** `Non-exhaustive \`switch\` on discriminated union`

Rejected: `switch (u.kind) { case "a": ...; /* missing "b" */ }`

[Details in subset.md#th0040--non-exhaustive-switch-on-discriminated-union](./subset.md#th0040--non-exhaustive-switch-on-discriminated-union)

Permanent — all variants must be covered.

---

## Recursion

### TH0050 — Cannot verify termination

**Message:** `Cannot verify termination; add \`@decreasing\` hint or restructure`

Rejected: `function f(n: bigint): bigint { ... return f(n - 1); ... /* non-structural */ }`

[Details in subset.md#th0050--cannot-verify-termination-add-decreasing-hint-or-restructure](./subset.md#th0050--cannot-verify-termination-add-decreasing-hint-or-restructure)

4 adds `@decreasing` JSDoc hints for non-structural recursion.

---

## Totality

`@total` is the Thales-TS claim that **a function always returns a value of its declared return type** — it terminates and has no observable failure modes. Three diagnostics enforce this contract: TH0066 (the annotation can't coexist with `@throws`), TH0067 (no failures may escape the body), and TH0070 (Lean's termination checker must accept the emitted `def`).

### TH0066 — `@total` and `@throws` declared together

**Message:** `` `@total` and `@throws` cannot both be declared on the same function; remove one ``

A function that may throw a declared error type does not always return a value of its declared return type — its emitted Lean signature is `Except E T`, not `T`. The two annotations make incompatible claims, so they are mutually exclusive at the source level (regardless of whether Lean would accept the emitted `def : Except E T`).

Example (rejected):

```typescript
/**
 * @total
 * @throws RangeError when age is negative
 */
function makeUser(name: string, age: number): User {
  if (age < 0) throw new RangeError('age must be non-negative');
  return { name, age };
}
```

Fix: drop `@total` if the function may genuinely fail (the `@throws` signature already encodes that the function does not diverge); drop `@throws` if the failure case is unreachable and you want the stronger guarantee.

---

### TH0067 — `@total` function has uncaught throw

**Message:** `` `@total` function has an uncaught `throw`; wrap it in `try`/`catch` or remove `@total` `` (or, for calls into `@throws`-annotated functions, `` `@total` function calls `@throws`-annotated `f` outside `try`/`catch`; catch the failure or remove `@total` ``)

Emitted at every uncaught throw event in the body of a `@total` function. A throw is "uncaught" if it is not lexically inside a `try` block whose `catch` clause handles it. A throw inside the `catch` handler itself counts as uncaught — `@total` requires the catch path to also have no escaping failures.

Example (rejected):

```typescript
/** @total */
function bad(n: number): number {
  if (n < 0) throw new RangeError('negative'); // TH0067
  return n;
}
```

Example (accepted):

```typescript
/** @throws RangeError */
function inner(n: number): number {
  if (n < 0) throw new RangeError('negative');
  return n;
}

/** @total */
function outer(n: number): number {
  try {
    return inner(n);
  } catch (e) {
    return 0;
  }
}
```

Fix: handle the failure case with `try`/`catch`, or annotate the function with `@throws` instead of `@total`.

---

### TH0070 — `@total` asserted but Lean rejects termination

**Message:** `` `@total` asserted but Lean could not prove termination: Lean reported: ... ``

Emitted when a `/** @total */` annotated function is emitted as `def` but Lean's termination checker rejects it. The message includes Lean's own error text (truncated to 400 characters).

Example (rejected):

```typescript
/** @total */
function fact(n: bigint): bigint {
  if (n === 0n) return 1n;
  return n * fact(n - 1n); // TH0070 here: Int subtraction is not a structural decrease
}
```

Fix: use structural recursion over a discriminated union type, or remove `@total` to fall back to `partial def` (accepted without termination proof).

[Details in subset.md](./subset.md#total-and-termination)

v1.1 adds `termination_by` / `decreasing_by` emission for common measure patterns.

**v1.0 limitation:** TH0070 only fires when `thales` is run inside a Lake project (it needs `lake env lean` to check the emitted Lean). Outside a Lake project, the check is skipped.

---

## Exceptions

### TH0060 — Unannotated throw

**Message:** `Function body contains \`throw\` but no \`@throws\` annotation`

Rejected: `throw new Error("...")` inside a function without `/** @throws E */` JSDoc.

Add a `@throws E` JSDoc annotation to the enclosing function, or remove the throw.

---

### TH0061 — Unused @throws annotation

**Message:** `Declared \`@throws\` but no corresponding \`throw\` in body`

Reserved for a future check that warns when a `@throws` annotation names a type that
is never actually thrown by the function body. Not emitted in v1.0.

---

### TH0063 — Thrown value must be a record type

**Message:** `Thrown value must be a record type`

Emitted when a `throw` statement's argument is a primitive literal — string, number,
boolean, `null`, or bigint. Thales requires thrown values to have named fields so
the emitted Lean pattern match can reference them.

Example (rejected):

```typescript
/** @throws string */
function parse(s: string): number {
  if (s === "") throw "empty";     -- TH0063: throwing a raw string
  return parseFloat(s);
}
```

Fix: throw a record. Either use a built-in like `new RangeError("empty")` or a
user-defined record type with a `message` field.

---

### TH0064 — Undeclared propagation

**Message:** `Function call throws T but enclosing function doesn't declare them in \`@throws\``

Emitted at a call site inside a `@throws`-annotated function body when the callee's
throws set includes types not covered by the enclosing function's `@throws` declaration.

Example (rejected):

```typescript
/** @throws RangeError */
function inner(): number { throw new RangeError("x"); return 1; }

/** @throws TypeError */          -- missing: RangeError
function outer(): number {
  return inner();                 -- TH0064 here: inner throws RangeError, not declared
}
```

Fix: add `RangeError` to `outer`'s `@throws` annotation, or wrap the call in `try/catch`.

---

## Directive

### TH9000 — Unused `@thales-expect-error` directive

**Message:** `Unused \`@thales-expect-error\` directive`

Emitted when an `@thales-expect-error` directive is followed by a code line
that produces no `TH####`. The directive is redundant and should be
removed.

Example (rejected):

```typescript
// @thales-expect-error TH0001
const x = 0;
```

---

### TH9001 — Directive code mismatch

**Message:** `\`@thales-expect-error\` expects TH#### but got TH####[, ...]`

Emitted when a directive declares a specific `TH####` but the applied
code line produces a different code (or set of codes). The message
lists every TH code that actually fired.

Example (rejected):

```typescript
// @thales-expect-error TH0001
const arr = [1];
arr[0] = 2; // actually emits TH0002
```

---

### TH9002 — Cannot emit: subset violations suppressed

**Message:** `Cannot emit: file contains subset violations suppressed by \`@thales-expect-error\``

Emitted in emit mode (the default) when any `TH####` was suppressed by
a matching directive. A suppressed violation is by construction not
embeddable into Lean; use `--no-emit` to exercise the subset check
without producing a `.lean` sidecar.

---

### TH9003 — Malformed `@thales-expect-error` directive

**Message:** `Malformed \`@thales-expect-error\` directive`

Emitted when a comment starts with a near-miss of the directive prefix
(e.g., `@thales-expect-erorr`, `@thales_expect_error`, or an ill-formed TH
code suffix) but does not match the strict grammar. The directive is
not applied for suppression.

Example (rejected):

```typescript
// @thales-expect-erorr TH0001   — typo, won't suppress
const x = 0;
```

---

### TH9004 — Emitted Lean code contains `sorry`

**Message:** (surfaced by the conformance harness, not by `thales` itself)

Emitted by the conformance harness when it detects `sorry` or `sorryAx`
in a `.lean` file that `thales` emitted. This indicates an emit-pipeline
soundness regression, not a user error. Do not work around by adding
`-- sorry` suppressions; file a bug against Thales.

This check applies only to `.lean` files that `thales` emits (not to
`Test/` WIP proofs or the runtime library).

---

## Refinement types

The four prelude refinement types (`Integer`, `Natural`, `Byte`, `Bit`)
are supported since v0.6. These codes enforce the refinement contract at
compile time.

### TH0080 — Literal value out of range for refinement type

**Message:** `Literal <N> out of range for <Type> (must be in [<lo>, <hi>])`

Emitted when a numeric literal is assigned to a refinement-typed slot and
the literal falls outside the type's range. `tsc` does not produce this
diagnostic (it sees the refinement types as plain `number`).

Range summary:

| Type    | Valid range                                       |
| ------- | ------------------------------------------------- |
| Integer | −9007199254740991 to 9007199254740991 (±2^53 − 1) |
| Natural | 0 to 9007199254740991                             |
| Byte    | 0 to 255                                          |
| Bit     | 0 or 1                                            |

Example (rejected):

```typescript
import { Byte } from '@thales/prelude';
// @thales-expect-error TH0080
const b: Byte = 256; // 256 > 255
```

Fix: use an in-range literal, or use the `as<T>(...)` constructor for
dynamic conversion (which throws `RangeError` at runtime if out of range).

---

### TH0081 — Value not assignable to refinement type without evidence

**Message:** `Value '<name>' of type 'number' is not assignable to '<Type>' without narrowing or constructor evidence`

Emitted when a `number`-typed expression is assigned to a refinement-typed
slot without any narrowing guard or constructor call to establish
membership evidence. `tsc` does not produce this diagnostic.

Example (rejected):

```typescript
import { Integer } from '@thales/prelude';
function wrap(n: number): Integer {
  // @thales-expect-error TH0081
  return n; // no evidence that n is a safe integer
}
```

Fix: narrow with a predicate guard (`if (isInteger(n)) { ... }`) or use
the throwing constructor (`asInteger(n)`) which validates at runtime.

[Details in subset.md](./subset.md#prelude-refinement-types)
