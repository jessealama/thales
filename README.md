# Thales

A TypeScript-to-Lean 4 compiler. Thales type-checks a safe subset of
TypeScript and emits a Lean 4 sidecar alongside the input `.ts` file,
turning your TypeScript module into a Lean module you can reason
about.

**Thales sits on top of strict TypeScript.** Every program Thales
accepts is also accepted by `tsc --strict` — we don't invent new
syntax or reinterpret existing type rules, so your editor tooling,
IDE integrations, and CI linters keep working. What Thales _does_ is
further restrict TS (rejecting mutation, classes, async, untyped
escapes, etc.) and enrich selected patterns — nullable unions,
`@throws`, `@total` — with Lean-visible semantics that TypeScript's
own type system cannot express. The result: a narrow, disciplined
subset of TS whose emitted Lean you can actually reason about.

## A quick taste

```typescript
type User = { name: string; age: number };

/** @throws RangeError when age is negative */
function makeUser(name: string, age: number): User {
  if (age < 0) throw new RangeError('age must be non-negative');
  return { name, age };
}

type NameList = { kind: 'nil' } | { kind: 'cons'; head: User; tail: NameList };

/** @total */
function firstName(xs: NameList): string | null {
  switch (xs.kind) {
    case 'nil':
      return null;
    case 'cons':
      return xs.head.name;
  }
}
```

Thales type-checks this against a strict subset of TypeScript and
emits Lean 4 where:

- `makeUser` becomes `def makeUser : String → Int → Except RangeError User`
  (failure mode visible in the signature; callers must `try`/`catch` or
  propagate via `@throws`).
- `firstName` becomes `def firstName : NameList → Option String`
  (Lean verifies termination from the structural recursion; nullability
  tracked in the type).

`@throws` and `@total` are mutually exclusive: a `@total` function makes
the stronger claim that no failure escapes, so it cannot also declare
one. See [`docs/subset.md`](docs/subset.md#total-and-termination).

## Install

```bash
git clone https://github.com/jessealama/thales.git
cd thales
lake build thales
```

## Usage

```bash
.lake/build/bin/thales foo.ts               # type-check + emit Foo.lean
.lake/build/bin/thales --no-emit foo.ts     # type-check only
.lake/build/bin/thales -o <dir> foo.ts      # emit into <dir>/Foo.lean
.lake/build/bin/thales --overwrite foo.ts   # emit, replacing existing Foo.lean
```

## Headline features

- **`Option` for nullable types.** `T | null` and `T | undefined` map
  to `Option T`. Narrowing on `=== null` / `!== null` works.
- **`@throws` for typed exceptions.** Functions that can throw declare
  their error types in JSDoc; the emitted Lean returns `Except E T`.
  `try`/`catch` desugars to a `match` on the `Except`. Catches use the
  standard TS form (`catch (e)` — untyped, as `tsc --strict` requires);
  Thales infers the caught type from the `try` body.
- **`@total` for "always returns a value" guarantees.** Default emission
  is `partial def` — non-total recursion is fine. `@total` is a stronger
  source-level claim: the function terminates (Lean's termination checker
  must accept it) _and_ no failure escapes (no uncaught `throw`, no
  uncaught call into a `@throws` callee). It is mutually exclusive with
  `@throws`; failures of either kind surface as clean diagnostics
  (TH0066/TH0067/TH0070).
- **Built-in bounded number types via `@thales/prelude` (v0.6).**
  `Integer`, `Natural`, `Byte`, and `Bit` are branded aliases of
  `number` in TypeScript and Lean Subtypes of `Float` in the emitted
  Lean. The chain is `Bit ⊆ Byte ⊆ Natural ⊆ Integer ⊆ number`.
  Numeric literals are checked at compile time (out-of-range →
  TH0080); assigning a plain `number` without a guard (`isInteger`,
  `isNatural`, …) or throwing constructor (`asInteger`, `asNatural`,
  …) is rejected with TH0081. Arithmetic operators always widen to
  `number`; narrow the result with a guard or constructor if you
  need the refinement type back.

## What's in the subset

Thales accepts a proper subset of what `tsc --strict` accepts. See
[`docs/subset.md`](docs/subset.md) for the full contract and
[`docs/errors.md`](docs/errors.md) for every `TH####` diagnostic code.
Out for v1.0: classes, mutation, async, `any`/`unknown`/intersection
types. See [`docs/future.md`](docs/future.md) for the roadmap.

## Generated Lean modules

Every emitted file opens with `import Thales.TS.Runtime`. The runtime
is a small Lean module (`Option'`, `Result`, error records,
`consoleLog` with JS-compatible number printing, array combinators,
`parseFloat`/`isNaN`) sized to v1 and designed so that the Lean path's
stdout matches the VM path byte-for-byte. See
[`docs/runtime.md`](docs/runtime.md) for the full surface.

## Testing

```bash
node scripts/run-examples.js --self-test     # harness regression
lake build ThalesTest                        # Lean unit tests
```

## License

[MIT](LICENSE)
