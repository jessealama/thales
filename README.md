# Thales

A TypeScript-to-Lean 4 compiler. Thales type-checks a safe subset of
TypeScript and emits a Lean 4 sidecar alongside the input `.ts` file,
turning your TypeScript module into a Lean module you can reason
about.

**Thales sits on top of strict TypeScript.** Every program Thales
accepts is also accepted by `tsc --strict` — we don't invent new
syntax or reinterpret existing type rules, so your editor tooling,
IDE integrations, and CI linters keep working. What Thales *does* is
further restrict TS (rejecting mutation, classes, async, untyped
escapes, etc.) and enrich selected patterns — nullable unions,
`@throws`, `@total` — with Lean-visible semantics that TypeScript's
own type system cannot express. The result: a narrow, disciplined
subset of TS whose emitted Lean you can actually reason about.

## A quick taste

```typescript
type User = { name: string; age: number };

/**
 * @throws RangeError when age is negative
 * @total
 */
function makeUser(name: string, age: number): User {
  if (age < 0) throw new RangeError("age must be non-negative");
  return { name, age };
}

function findAge(users: User[], name: string): number | null {
  for (const u of users) {
    if (u.name === name) return u.age;
  }
  return null;
}
```

Thales type-checks this against a strict subset of TypeScript and
emits Lean 4 where:
- `makeUser` becomes `def makeUser : String → Int → Except RangeError User`
  (Lean verifies termination; failure modes visible in the signature).
- `findAge` becomes `def findAge : List User → String → Option Int`
  (nullability tracked in the type).

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
- **`@total` for opt-in termination proofs.** Default emission is
  `partial def` — non-total recursion is fine. `@total` forces Lean's
  termination checker; failure surfaces as a clean diagnostic.

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
