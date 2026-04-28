# Thales-TS Error Code Reference

## Error code alignment

Every thales diagnostic either:

- uses a `TSXXXX` code that tsc would also emit at the same line for the
  same input (so thales's type-check output can be compared to tsc's by
  `(file, line, code)` equality), or
- uses a `TH####` code, listed below, for subset-specific violations (these
  have no tsc equivalent and exist only because thales is stricter than tsc
  about what programs it is willing to embed into Lean).

Extra `TH####` diagnostics never cause a conformance failure. A `TSXXXX`
diagnostic reported by thales that tsc would not produce is a bug; report it.
Column positions are not currently compared by the conformance harness
because thales and tsc disagree on per-diagnostic anchoring, but they are
displayed in diagnostics for human readability.

See `docs/superpowers/specs/2026-04-21-conformance-harness-design.md` for
the full contract and harness details.

## Overview

`thales` emits two categories of diagnostics:

- **TS####** — Inherited TypeScript compiler diagnostics (from standard `tsc` behavior)
- **TH####** — Thales-TS subset violations (errors enforcing the pure-functional, Lean-embeddable subset)

This reference lists all 18 subset `TH####` codes plus the 4 directive
codes (TH9000–TH9003) with minimal detail. For full explanation,
rationale, and idiomatic replacements, see [subset.md](./subset.md).

## Summary

| Code | Category | Short Message | Addressed By |
|------|----------|---------------|--------------|
| TH0001 | Mutation | Cannot reassign variable | 1.5 |
| TH0002 | Mutation | Cannot assign to array element | 1.5 |
| TH0003 | Mutation | Cannot assign to object property | 1.5 |
| TH0004 | Mutation | Cannot call mutating method | 1.5 |
| TH0005 | Mutation | Cannot mutate variable captured by enclosing scope | 1.5 |
| TH0010 | Control flow | Loop not supported | 1.5 |
| TH0011 | Control flow | throw/try/catch not supported | **Partially lifted in v1.0** — `@throws` + try/catch now accepted |
| TH0012 | Control flow | async/await not supported | 6+ |
| TH0020 | Types | `any` not permitted | permanent |
| TH0021 | Types | `unknown` not permitted in user code | 3 |
| TH0022 | Types | Union must be discriminated | permanent |
| TH0023 | Types | Intersection types not supported | permanent |
| TH0024 | Types | keyof/conditional/mapped types not supported | permanent |
| TH0025 | Types | null/undefined types not supported | **Lifted in v1.0** — `T \| null` now emits as `Option T` |
| TH0030 | Declarations | `class` not supported | 2 |
| TH0031 | Declarations | Inheritance (`extends`) not supported | 6+ |
| TH0040 | Matching | Non-exhaustive switch on discriminated union | permanent |
| TH0050 | Recursion | Cannot verify termination | 4 |
| TH0070 | Totality | `@total` asserted but Lean rejects termination | restructure or drop `@total` |
| TH0060 | Exceptions | Unannotated `throw` | Annotate with `@throws E` |
| TH0061 | Exceptions | Unused `@throws` annotation | permanent |
| TH0063 | Exceptions | Thrown value must be a record type | Throw a record, e.g. `new RangeError("...")` |
| TH0064 | Exceptions | Undeclared propagation | Expand `@throws` declaration |
| TH9000 | Directive | Unused `@thales-expect-error` directive | 0.5 |
| TH9001 | Directive | Directive code mismatch | 0.5 |
| TH9002 | Directive | Cannot emit: subset violations suppressed | 0.5 |
| TH9003 | Directive | Malformed `@thales-expect-error` directive | 0.5 |

---

## Mutation

### TH0001 — Cannot reassign variable

**Message:** `Cannot reassign variable`

Rejected: `let x = 0; x = 1;`

[Details in subset.md#th0001--cannot-reassign-variable](./subset.md#th0001--cannot-reassign-variable)

1.5 adds immutable `let` bindings via `Id.run do`.

---

### TH0002 — Cannot assign to array element

**Message:** `Cannot assign to array element; use \`.concat\` or return a new array`

Rejected: `arr[0] = 99;`

[Details in subset.md#th0002--cannot-assign-to-array-element-use-concat-or-return-a-new-array](./subset.md#th0002--cannot-assign-to-array-element-use-concat-or-return-a-new-array)

1.5 adds persistent array update via `Array.set` + functional update syntax.

---

### TH0003 — Cannot assign to object property

**Message:** `Cannot assign to object property; construct a new object`

Rejected: `obj.x = 10;`

[Details in subset.md#th0003--cannot-assign-to-object-property-construct-a-new-object](./subset.md#th0003--cannot-assign-to-object-property-construct-a-new-object)

1.5 adds record update via spread syntax (`{...obj, x: 10}`).

---

### TH0004 — Cannot call mutating method

**Message:** `Cannot call mutating method`

Rejected: `arr.push(42);`

[Details in subset.md#th0004--cannot-call-mutating-method](./subset.md#th0004--cannot-call-mutating-method)

1.5 replaces mutating methods (`.push`, `.pop`, `.splice`, `.sort`, `.reverse`) with functional equivalents.

---

### TH0005 — Cannot mutate variable captured by enclosing scope

**Message:** `Cannot mutate variable captured by enclosing scope`

Rejected: `let sum = 0; arr.forEach(x => { sum += x; });`

[Details in subset.md#th0005--cannot-mutate-variable-captured-by-enclosing-scope](./subset.md#th0005--cannot-mutate-variable-captured-by-enclosing-scope)

1.5 adds mutable captured variables via reference cells.

---

## Control flow

### TH0010 — Loop not supported

**Message:** `Loop not supported; use recursion or array methods`

Rejected: `for (let i = 0; i < n; i++) { ... }`

[Details in subset.md#th0010--loop-not-supported-use-recursion-or-array-methods](./subset.md#th0010--loop-not-supported-use-recursion-or-array-methods)

1.5 adds loops via `Id.run do`.

---

### TH0011 — throw/try/catch not supported *(partially lifted in v1.0)*

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

### TH0025 — null/undefined types not supported *(lifted in v1.0)*

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

### TH0070 — `@total` asserted but Lean rejects termination

**Message:** `` `@total` asserted but Lean could not prove termination: Lean reported: ... ``

Emitted when a `/** @total */` annotated function is emitted as `def` but Lean's termination checker rejects it. The message includes Lean's own error text (truncated to 400 characters).

Example (rejected):
```typescript
/** @total */
function fact(n: bigint): bigint {
  if (n === 0n) return 1n;
  return n * fact(n - 1n);   // TH0070 here: Int subtraction is not a structural decrease
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
const arr = [1]; arr[0] = 2;  // actually emits TH0002
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
