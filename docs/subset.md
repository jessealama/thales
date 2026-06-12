# Thales-TS 0.6 Subset Reference

## Overview

Thales-TS 0.6 is a pure-functional subset of TypeScript with a mechanical shallow embedding into Lean 4. It is enforced by `thales` and can be translated to Lean 4 source with `thales` (emit is the default; `--no-emit` skips it). The existing Thales JavaScript VM is unchanged; Thales-TS runs on it via the usual erase-and-execute path.

v0.6 adds four built-in bounded number types (`Integer`, `Natural`, `Byte`, `Bit`) shipped via `@thales/prelude`. See the dedicated section below for details.

Thales-TS is **not** full TypeScript. It excludes escaping mutation (function-local non-escaping mutation is in subset, emitted as `Id.run do`), unannotated exceptions, async I/O, classes, and several advanced type constructs in order to keep every accepted program mechanically translatable to terminating Lean 4 code. If your program compiles under `thales`, it has a Lean 4 image — and the behavior of the two paths is verified by the example corpus.

## Conformance contract

Thales-TS defines itself relative to Microsoft's TypeScript via an executable
contract enforced by the example harness (`scripts/run-examples.js`):

1. **Subset on rejection.** Every `file(line, col): error TSXXXX` that
   `tsc -p tsconfig.json --noEmit` (with `--ignoreConfig` when invoked
   per-file) produces must also appear in thales's output at the same line with
   the same `TSXXXX` code.
2. **No invented TS codes.** thales must not report a `TSXXXX` diagnostic that
   tsc doesn't also produce at the same line.
3. **Subset-local extras.** thales may additionally report `TH####` diagnostics
   for subset violations; these never count against the contract.
4. **Runtime byte-exactness.** When both tsc and thales accept a file, running
   it via `tsx input.ts` and via `thales input.ts && lake env lean input.lean`
   must produce identical stdout, stderr, and exit code.

The reference configuration is `tsconfig.json` at the repo root:
`strict` + `noUncheckedIndexedAccess` + ES2022 target/lib (plus DOM for `console`).
The `typescript` and `tsx` versions are pinned in `package.json`.

### The `@thales-expect-error` directive

A line-comment of the form `// @thales-expect-error [TH####]` immediately
above a code line suppresses all `TH####` diagnostics on that line (and
optionally asserts that a specific code is among them), mirroring tsc's
`@ts-expect-error`.

```typescript
let x = 0;
// @thales-expect-error TH0001
x = 1;
```

Semantics at a glance:

- **Match:** at least one TH on the applied line; the declared code
  (if any) is among them. All TH on that line are suppressed.
- **Wrong code:** TH fires but the declared code differs. `TH9001` is
  emitted; original TH diagnostics are not suppressed.
- **No TH:** the applied line is clean. `TH9000` (unused directive).
- **Malformed:** a near-miss prefix (`@thales-expect-erorr`, …). `TH9003`;
  no suppression.
- **Emit mode:** a file with any suppressed TH cannot be emitted to
  Lean; `TH9002` is raised and no `.lean` sidecar is written. The
  directive is a documentation primitive, not a partial-build mechanism.

See `docs/errors.md` for TH9000–TH9003 details, and the conformance corpus
under `tests/conformance/reject/` for one canonical demonstration per `TH####` code.

## In-scope features

| Kind         | Detail                                                                                                                                           |
| ------------ | ------------------------------------------------------------------------------------------------------------------------------------------------ |
| Primitives   | `boolean`, `string`, `number` (→ Lean `Float`), `bigint` (→ Lean `Int`)                                                                          |
| Records      | `interface` and `type` aliases — nominal by declaration                                                                                          |
| Arrays       | `T[]` as immutable `Array T`; `arr[i]` returns `Option<T>`                                                                                       |
| Tuples       | `[A, B]`, `[A, B, C]`, ... → Lean `×` / fixed structures                                                                                         |
| Unions       | Discriminated unions (shared `kind` field of string-literal type) → Lean inductive; nullable unions (`T \| null`, `T \| undefined`) → `Option T` |
| Generics     | Parametric only (`<T>`, `<T, U>`)                                                                                                                |
| Values       | `const`, `let`, `var`; function-local non-escaping mutation (`x = e`, `x OP= e`, `x++`/`x--`) emitted as `Id.run do` with `let mut` (#24)        |
| Functions    | `function` declarations and `const f = (...) => ...` arrows                                                                                      |
| Recursion    | Structural or with `@decreasing` hint; all functions must terminate in 0.5                                                                       |
| Control flow | `if`/`else`, ternary, `switch` (exhaustive on a discriminated union)                                                                             |
| Modules      | `import`/`export` of values and types                                                                                                            |
| Stdlib       | `Option<T>`, `Result<T, E>`, array `.map`/`.filter`/`.reduce`/`.concat`/`.length`/`.slice`                                                       |
| Refinements  | `Integer`, `Natural`, `Byte`, `Bit` from `@thales/prelude` — Lean Subtypes of `Float`; chain `Bit ⊆ Byte ⊆ Natural ⊆ Integer ⊆ number`           |

## Out-of-scope features

Each restriction below is identified by a `TH####` diagnostic code produced by `thales`.

---

### TH0001 — Cannot reassign variable

**Category:** Mutation

Function-local non-escaping mutation is **in subset** since #24: a binding
whose every reference (read or write) stays in the declaring function's own
body may be reassigned, and the function lowers to `Id.run do` with
`let mut`. Parameters count as initialized locals (mutating them never
affects the caller). TH0001 covers the still-rejected forms:

Rejected (module level):

```typescript
let count = 0;
count = count + 1; // TH0001: top-level bindings stay immutable
```

Also still rejected under TH0001:

- the logical assignment operators `&&=`, `||=`, `??=` (short-circuit
  semantics; deferred);
- reassigning a `let` declared without an initializer (`let mut` needs
  one — give the declaration an initial value);
- reassigning a variable whose narrowing the emitter relies on
  (null- or undefined-tested, or refinement-predicate-tested, in a
  condition);
- mutation inside arrow/function-expression bodies (only declared
  functions lower through the do-mode path in v1);
- mutation in a function containing a `switch` shape do-mode cannot lower
  (an arm that falls through via `break`, a `default` arm, or a scrutinee
  that is not a discriminated-union field access);
- mutation in a function whose body contains `try`/`catch` (the exception
  path emits pure `Except` match-chains do-mode cannot thread through;
  mutation _inside_ the `try` is the separate TH0007);
- mutation in a function that reads a null/undefined-tested or
  predicate-tested variable outside its test (the pure path bakes that
  narrowing into its `match`/`dite` lowering; do-mode carries no such
  evidence).

Idiomatic replacement where mutation stays rejected:

```typescript
const count = 0;
const nextCount = count + 1;
```

---

### TH0002 — Cannot assign to array element; use `.concat` or return a new array

**Category:** Mutation

Rejected:

```typescript
const arr = [1, 2, 3];
arr[1] = 99;
```

Idiomatic replacement:

```typescript
const arr = [1, 2, 3];
const updated = arr.slice(0, 1).concat([99]).concat(arr.slice(2));
```

Lean's `Array` type supports functional update (`Array.set`), but index-assignment syntax implies in-place mutation semantics that cannot be expressed in pure Lean without threading state explicitly. 0.5 treats arrays as persistent.

---

### TH0003 — Cannot assign to object property; construct a new object

**Category:** Mutation

Rejected:

```typescript
const pt = { x: 1, y: 2 };
pt.x = 10;
```

Idiomatic replacement:

```typescript
const pt = { x: 1, y: 2 };
const moved = { ...pt, x: 10 };
```

Record update via spread maps cleanly to Lean structure update syntax (`{ pt with x := 10 }`). Direct property assignment implies a mutable heap that has no first-class shallow embedding in pure Lean.

---

### TH0004 — Cannot call mutating method

**Category:** Mutation

Rejected:

```typescript
const items: number[] = [];
items.push(42);
```

Idiomatic replacement:

```typescript
const items: number[] = [];
const withItem = items.concat([42]);
```

Methods like `.push`, `.pop`, `.splice`, `.sort`, and `.reverse` mutate their receiver. Their Lean equivalents all return new arrays. Allowing these calls would break the pure-functional invariant that makes the Lean embedding straightforward.

---

### TH0005 — Cannot mutate variable captured by enclosing scope

**Category:** Mutation

Rejected:

```typescript
let total = 0;
[1, 2, 3].forEach((n) => {
  total += n;
});
```

Idiomatic replacement:

```typescript
const total = [1, 2, 3].reduce((acc, n) => acc + n, 0);
```

Mutable captured variables require reference cells (`ST.Ref` or `IO.Ref`) in Lean. Supporting them correctly would require full effect-system analysis, which is deferred beyond 0.5.

---

### TH0010 — Loop not supported; use recursion or array methods

**Category:** Control flow

**Status:** Partially lifted. The admitted shapes are described below;
everything else still fires TH0010.

#### Admitted shapes

The following loop forms are accepted inside declared functions that are
do-mode-lowerable (no `@throws`, no `try`/`catch`, no do-mode-poisoning
constructs):

**`for-of` over an array identifier or literal:**

```typescript
function sum(xs: number[]): number {
  let total = 0;
  for (const x of xs) {
    total += x;
  }
  return total;
}
```

Conditions: the right-hand side is a simple identifier of array type or an
array literal; the loop variable is `const x` or `let x` (simple identifier,
not a destructuring pattern); the loop variable is not reassigned in the body.
Lowers to `for x in xs do` inside `Id.run do`.

**Canonical C-style `for`:**

```typescript
function indexWeight(xs: number[]): number {
  let total = 0;
  for (let i = 0; i < xs.length; i++) {
    total += i;
  }
  return total;
}
```

Conditions: init is `let i = 0`; test is `i < B` where `B` is a non-negative
integer literal or `arr.length` for an array-typed parameter `arr` (a
`string`-typed `.length` bound is rejected — Lean range bounds need
`Array.size`, and string length semantics diverge); update is `i++`; the
bound array (if any) is not reassigned in the body. Lowers to a Lean range
loop (`for i in [0:B] do`) inside `Id.run do`.

**`while` and `do`/`while`**:

```typescript
function leftPad(str: string, len: number, ch: string): string {
  let pad = str;
  while (pad.length < len) {
    pad = ch + pad;
  }
  return pad;
}
```

Any boolean-typed test expression is accepted (conditions must be
boolean — see TH0026). `while` lowers to Lean do-notation
`while`; `do`/`while` lowers to `repeat ... until !(test)` (body runs at
least once, as in TS). Both are backed by a partial combinator — fine for
evaluation (the byte-match contract is unaffected), opaque to termination
proofs — so they are **mutually exclusive with `@total`** (TH0068),
mirroring the `@total`/`@throws` exclusivity. A do-while whose body has a
loop-level `continue` stays rejected: TS `continue` jumps to the test,
but Lean's `repeat ... until` re-enters the body without checking it.

**Non-canonical C-style `for`**:
any `for (init; test; update)` where init is empty, a bare expression, or
a single-identifier `let`/`const` declarator with an initializer.
Desugars to `init; while (test) { body; update }`, so it inherits the
`while` rules (including the `@total` exclusion, TH0068). A loop-level
`continue` is rejected when an update clause exists (the desugared body
would skip the update where TS runs it before re-testing). The canonical
`for (let i = 0; i < B; i++)` shape keeps its structural range lowering
above — including its operand restrictions — and stays `@total`-friendly.

**Inside admitted loops:** unlabeled `break`, `continue`, early `return`, and
mutation following the TH0001–TH0007 rules are all accepted.

#### Still rejected

- `for-in`, `for await`.
- Canonical-shaped `for` whose bound is not a non-negative integer
  literal or an array-typed `arr.length` (e.g. a `string`-typed
  `s.length`) — the canonical shape never falls back to the while-desugar.
- `var` loop-variable heads; destructuring or expression loop-variable
  heads in `for-of`.
- `for-of` with a call expression on the right-hand side.
- Loop variable or bound array reassigned in a canonical-for body.
- Labeled `break`/`continue`.
- Loop-level `continue` in a do-while body, or in a general `for` body
  when an update clause exists.
- Any loop at module level, inside a `@throws`-annotated function, or in
  a function with `try`/`catch`.
- `while`/`do-while`/general `for` inside a `@total` function (TH0068).

For the still-rejected cases, idiomatic replacements are recursive helpers or
higher-order array methods:

```typescript
// still-rejected loop (e.g. module-level, or inside @throws/@total) → recursion
function go(i: number): void {
  if (i >= arr.length) return;
  process(arr[i]);
  return go(i + 1);
}
go(0);

// for-of side-effects without mutation → forEach
arr.forEach(process);
```

---

### `@throws` and exception handling

**Lifted in v1.0** (previously TH0011 for `throw`; try/catch now accepted with restrictions).

Functions that throw are annotated with `/** @throws E1 | E2 | ... */` JSDoc. The annotated
function's return type becomes `Except (E1 ⊕ E2 ⊕ ...) R` in Lean. `throw new E(msg)` inside
such a function emits as `Except.error (.inl/.inr E.mk msg)` with the appropriate Sum injection.

```typescript
/** @throws RangeError */
function divide(a: number, b: number): number {
  if (b === 0) throw new RangeError('division by zero');
  return a / b;
}
```

Emits as:

```lean
def divide (a : Float) (b : Float) : Except RangeError Float :=
  if b == 0.0 then .error (RangeError.mk "division by zero")
  else .ok (a / b)
```

**Error types:** Predeclared built-in error types are `Error`, `TypeError`, `RangeError`,
`SyntaxError`, `ReferenceError`. Each is a Lean structure with a single `message : String` field
defined in `Thales.TS.Runtime`. `Error` is NOT a supertype of `TypeError` — catches are exact.

**Multiple throws:** `@throws TypeError | RangeError` emits the error type as `TypeError ⊕ RangeError`.
`throw new TypeError(msg)` emits as `.error (.inl ...)` and `throw new RangeError(msg)` as `.error (.inr ...)`.

**try/catch desugars to match on Except:**

`try { return f(args); } catch (e) { handler }` where `f` is `@throws E` emits as:

```lean
match f args with
| .ok v => v   -- or .ok v if outer function also @throws
| .error e => [handler]
```

The catch variable `e` is bound to the error value in the catch body.

**Propagation:** Calls to `@throws`-annotated functions inside another `@throws`-annotated function
body propagate the throws automatically. Each `const x = f(args)` where `f` is `@throws E` emits as:

```lean
match f args with
| .ok x => [rest]
| .error e => .error e  -- propagate
```

The enclosing function's `@throws` annotation must declare all error types that can propagate
through it from callees. Missing declaration → TH0064.

Calls inside a `try` block (wrapped by a matching `catch`) are NOT counted as propagated —
the catch handles them locally.

**`no finally` / no multi-catch in v1.0:** Only single-catch try/catch is supported. `finally`
and catch clauses with multiple handlers are out of scope.

**TH0060 — Unannotated throw:**

A `throw` statement inside a function without `@throws` annotation emits TH0060.

**TH0063 — Non-record throw:**

A `throw` of a primitive literal (string, number, boolean, `null`, bigint) emits
TH0063. Thrown values must be records so their fields are nameable in the emitted
Lean pattern match.

**TH0064 — Undeclared propagation:**

A call to a `@throws`-annotated function that is not wrapped in a catching try/catch
must be covered by the enclosing function's own `@throws` declaration. Missing
declaration → TH0064 at the call site. Applies even when the caller has no `@throws`
of its own: a silent caller of a throwing function is explicitly rejected so effects
stay visible through the call graph.

**On `catch (e: E)`:** `tsc --strict` rejects typed catch variables (TS1196);
only `catch (e)`, `catch (e: unknown)`, and `catch (e: any)` are valid standard
TS. Thales accepts untyped catches and infers the caught type from the `try`
body's `Except` shape.

---

### TH0012 — `async`/`await` not supported

**Category:** Control flow

Rejected:

```typescript
async function fetchUser(id: string): Promise<User> {
  const resp = await fetch(`/users/${id}`);
  return resp.json();
}
```

Idiomatic replacement:

```typescript
// Pure function — no I/O, no await. Callable from anywhere.
function userGreeting(user: { name: string }): string {
  return `Hello, ${user.name}!`;
}

// Orchestration stays outside Thales-TS — written in plain TS
// or another environment. Thales-TS proves things about the pure core.
```

Async is an effect, not a value. Thales-TS proves things about pure code. The recommended pattern is to extract the pure computation into a Thales-TS function and keep the async orchestration outside the subset (plain TypeScript, or handwritten Lean `IO` code). Typed exceptions and async are 3+ work.

---

### TH0020 — `any` is not permitted

**Category:** Types

Rejected:

```typescript
function identity(x: any): any {
  return x;
}
```

Idiomatic replacement:

```typescript
function identity<T>(x: T): T {
  return x;
}
```

`any` erases type information entirely, making a typed Lean embedding impossible. The Lean image would need `Lean.Expr` or untyped metaprogramming, which is far outside 0.5 scope. Use a type parameter instead.

---

### TH0021 — `unknown` is not permitted in user code

**Category:** Types

Rejected:

```typescript
function parse(raw: unknown): string {
  return String(raw);
}
```

Idiomatic replacement:

```typescript
function parse(raw: string): string {
  return raw;
}
```

`unknown` requires runtime type narrowing before use. The narrow-before-use pattern can be modelled, but the type-level machinery needed to track narrowing in Lean is beyond 0.5. Inputs should be fully typed at their call site.

---

### TH0022 — Union must be discriminated

**Category:** Types

Rejected:

```typescript
type StringOrNumber = string | number;

function double(x: StringOrNumber): StringOrNumber {
  if (typeof x === 'number') return x * 2;
  return x + x;
}
```

Idiomatic replacement:

```typescript
type Value = { kind: 'num'; value: number } | { kind: 'str'; value: string };

function double(x: Value): Value {
  if (x.kind === 'num') return { kind: 'num', value: x.value * 2 };
  return { kind: 'str', value: x.value + x.value };
}
```

Primitive unions (`string | number`) require `typeof` guards for safe access and map to Lean `Sum` types awkwardly without a canonical tag. Discriminated unions with a `kind` string literal map cleanly to Lean inductives and generate exhaustiveness checks automatically.

---

### TH0023 — Intersection types are not supported

**Category:** Types

Rejected:

```typescript
type Named = { name: string };
type Aged = { age: number };
type Person = Named & Aged;
```

Idiomatic replacement:

```typescript
interface Person {
  name: string;
  age: number;
}
```

Intersection types in TypeScript model mixin composition and can express non-denotable combinations. The shallow embedding flattens them to Lean structures, which requires a deterministic merge rule that is not yet defined. Flatten to a single `interface` for 0.5.

---

### TH0024 — `keyof`/conditional/mapped types are not supported

**Category:** Types

Rejected:

```typescript
type ReadOnly<T> = { readonly [K in keyof T]: T[K] };
type IsString<T> = T extends string ? 'yes' : 'no';
```

Idiomatic replacement:

```typescript
// Define the concrete readonly record directly:
interface ReadOnlyPoint {
  readonly x: number;
  readonly y: number;
}
```

These constructs are type-level programs; translating them to Lean requires dependent types or macro metaprogramming. They are deferred to a future version with a type-level elaboration pass.

---

### TH0026 — Condition must be boolean

**Category:** Types

Every condition position — `if`, `while`, `do`/`while`, the `for` test
clause, and the ternary — must have type `boolean`. tsc accepts any type
in these positions and applies JS truthiness (`0`, `''`, `NaN`, `null`,
`undefined` are falsy); Lean has no truthiness coercion, so a non-boolean
condition would emit a branch the Lean stage cannot compile, violating
the accept clause of the conformance contract.

Rejected:

```typescript
function f(n: number): number {
  if (n) {
    // TH0026: Condition must be boolean, got 'number'
    return 1;
  }
  return 0;
}
```

Idiomatic replacement:

```typescript
function f(n: number): number {
  if (n !== 0) {
    return 1;
  }
  return 0;
}
```

Mirroring truthiness with a runtime coercion (`truthy : Float → Bool`
handling `NaN` and `-0`) is a possible future widening; rejection is the
v1 boundary.

---

### Nullable types: `T | null` and `T | undefined` → `Option T`

**Lifted in v1.0** (previously TH0025).

`T | null`, `T | undefined`, and `T | null | undefined` are accepted and emitted
as Lean `Option T`. The restriction to discriminated-union form does not apply
to nullable unions.

```typescript
function findName(id: string): string | null {
  if (id === '1') return 'Alice';
  return null;
}

function describe(name: string | null): string {
  if (name === null) return 'no name found';
  return 'found a name';
}
```

Emits as:

```lean
def findName (id : String) : Option String :=
  if id == "1" then .some "Alice" else .none

def describe (name : Option String) : String :=
  match name with
  | .none => "no name found"
  | .some name => "found a name"
```

**Usage-site translations:**

| TypeScript                                     | Emitted Lean |
| ---------------------------------------------- | ------------ |
| `null` literal                                 | `.none`      |
| `return expr` in `Option T` function           | `.some expr` |
| `x === null` / `x === undefined` / `x == null` | `x.isNone`   |
| `x !== null` / `x !== undefined` / `x != null` | `x.isSome`   |
| `x ?? y`                                       | `x.getD y`   |

**Narrowing:**

`if (x === null)` / `if (x !== null)` guards on an `Option T` variable emit as
`match x with | .none => ... | .some x => ...`, rebinding `x` to `T` in the
non-null arm. `if (x === undefined)` behaves identically.

**Limitations in v1.0:**

- Bare `null` and `undefined` types in non-nullable positions are still rejected (TH0025 remains for standalone `null` or `undefined` types that are not part of a two-member nullable union).
- Truthiness narrowing (`if (x)`) does not auto-narrow `Option T`; use explicit `=== null` equality guards instead. This is because `Option<0>` or `Option<false>` have inhabitants that are falsy in JS but not provably none in Lean.
- Post-`if` control-flow narrowing (narrowing `x` to `T` after `if (x === null) return ...`) is not yet implemented; the type checker still sees `x` as `Option T` after the guard statement.

---

### TH0030 — `class` not supported

**Category:** Declarations

Rejected:

```typescript
class Counter {
  private count: number = 0;
  increment(): void {
    this.count++;
  }
  get(): number {
    return this.count;
  }
}
```

Idiomatic replacement:

```typescript
interface Counter {
  count: number;
}
function increment(c: Counter): Counter {
  return { count: c.count + 1 };
}
function getCount(c: Counter): number {
  return c.count;
}
```

Classes combine mutable state, method dispatch, and prototype-chain semantics — none of which have a direct shallow embedding in pure Lean. Classes are a 2 candidate via a `structure` + `namespace` desugaring, once the mutation story is resolved.

---

### TH0031 — Inheritance (`extends`) not supported

**Category:** Declarations

Rejected:

```typescript
class Animal {
  speak(): string {
    return '...';
  }
}
class Dog extends Animal {
  speak(): string {
    return 'woof';
  }
}
```

Idiomatic replacement:

```typescript
type Animal = { kind: 'dog' } | { kind: 'cat' };
function speak(a: Animal): string {
  switch (a.kind) {
    case 'dog':
      return 'woof';
    case 'cat':
      return 'meow';
  }
}
```

Single-dispatch method inheritance maps to `structure extends` in Lean, but virtual dispatch and override semantics require typeclass resolution that goes beyond the 0.5 shallow embedding. Discriminated unions with pattern matching cover the common use case.

---

### TH0040 — Non-exhaustive `switch` on discriminated union

**Category:** Matching

Rejected:

```typescript
type Shape = { kind: 'circle'; r: number } | { kind: 'square'; side: number };

function area(s: Shape): number {
  switch (s.kind) {
    case 'circle':
      return Math.PI * s.r * s.r;
    // missing "square" case
  }
}
```

Idiomatic replacement:

```typescript
function area(s: Shape): number {
  switch (s.kind) {
    case 'circle':
      return Math.PI * s.r * s.r;
    case 'square':
      return s.side * s.side;
  }
}
```

Lean's `match` expressions must be exhaustive; the compiler rejects any missing case. Thales-TS enforces the same discipline up front so that the emitted Lean is always well-formed. Add a branch for every variant.

---

### TH0050 — Cannot verify termination; add `@decreasing` hint or restructure

**Category:** Recursion

Rejected:

```typescript
function collatz(n: bigint): bigint {
  if (n === 1n) return 1n;
  if (n % 2n === 0n) return collatz(n / 2n);
  return collatz(3n * n + 1n);
}
```

Idiomatic replacement:

```typescript
/** @decreasing n */
function collatz(n: bigint, fuel: bigint): bigint {
  if (fuel === 0n || n === 1n) return n;
  if (n % 2n === 0n) return collatz(n / 2n, fuel - 1n);
  return collatz(3n * n + 1n, fuel - 1n);
}
```

Lean's kernel requires all functions to provably terminate. When `thales` cannot infer a structural decreasing argument automatically, it emits TH0050. Add a `@decreasing` JSDoc hint naming the decreasing parameter, or introduce a `fuel` counter. Functions that cannot be shown to terminate are not permitted in 0.5.

---

### `@total` and termination

Every function in a Thales-TS program is emitted as `partial def` by default. A `partial def` in Lean 4 is accepted without termination proof — it can loop. This is the safe default: the JS VM and the emitted Lean both execute the function, and if the function terminates in JS, it terminates in Lean too.

To opt into Lean's termination checker for a specific function, annotate it with `@total` in its JSDoc:

```typescript
/** @total */
function sum(xs: NatList): bigint {
  switch (xs.kind) {
    case 'nil':
      return 0n;
    case 'cons':
      return xs.head + sum(xs.tail);
  }
}
```

`@total` is a claim about the function's TypeScript-level behavior: **the function always returns a value of its declared return type** — it terminates _and_ it has no observable failure modes. Two checks enforce this:

1. **No declared failures.** The function may not also carry `@throws`. (TH0066.)
2. **No escaping failures.** The body must contain no uncaught `throw` and no uncaught call to a `@throws`-annotated function. A throw fully handled by an enclosing `try`/`catch` is fine; a throw inside the `catch` handler itself is not. (TH0067.)

Under the hood, `@total` causes the function to be emitted as a plain `def` (not `partial def`). Lean's default termination checker must accept it. For structural recursion over discriminated unions (the typical case), Lean infers the measure automatically.

If Lean rejects the termination proof, `thales` emits **TH0070** with Lean's own error text:

```
input.ts(5,1): error TH0070: `@total` asserted but Lean could not prove termination:
  Lean reported: fail to show termination for Input.fact ...
```

**What `@total` does and doesn't do:**

- Emits as `def` instead of `partial def`.
- Lean's default structural-recursion checker must accept the function as-is.
- No `termination_by` or `decreasing_by` clauses are emitted. If Lean cannot prove termination automatically, you must restructure the function (or remove `@total`).
- `@total` and `@throws` are mutually exclusive — a `@total` function has no observable failure modes by definition. To express "this function always returns or throws a known error type, never diverges," use `@throws` alone; the emitted Lean type already encodes finiteness via `Except`.

**Typical patterns that Lean accepts with `@total`:**

- Structural recursion over a discriminated-union type (e.g., a tree or list defined as a `type` alias).
- Functions where Lean can observe the recursive argument is a direct sub-expression of the input.

**Typical patterns that fail with `@total`:**

- Integer arithmetic decrease: `fact(n - 1n)` on `bigint` (mapped to Lean `Int`) has no structural decrease. Lean rejects.
- `xs.slice(1)` on arrays: Lean cannot prove the sliced array is smaller. Lean rejects.

**v1.0 limitation:** The termination check is only performed when `thales` is run from inside a Lake project (the binary walks up from the input file to find a `lakefile.lean` or `lakefile.toml`). When run from outside a Lake project, the check is skipped and TH0070 cannot fire. This limitation is documented; `termination_by` and `decreasing_by` emission are deferred to v1.1.

---

## Translation examples

### 1. Identity function

TypeScript:

```typescript
function identity<T>(x: T): T {
  return x;
}
```

Lean 4:

```lean
def identity {T : Type} (x : T) : T :=
  x
```

---

### 2. Record type

TypeScript:

```typescript
interface Point {
  x: number;
  y: number;
}

function translate(p: Point, dx: number, dy: number): Point {
  return { x: p.x + dx, y: p.y + dy };
}
```

Lean 4:

```lean
structure Point where
  x : Float
  y : Float

def translate (p : Point) (dx dy : Float) : Point :=
  { p with x := p.x + dx, y := p.y + dy }
```

---

### 3. Discriminated union

TypeScript:

```typescript
type Shape = { kind: 'circle'; r: number } | { kind: 'square'; side: number };

function area(s: Shape): number {
  switch (s.kind) {
    case 'circle':
      return Math.PI * s.r * s.r;
    case 'square':
      return s.side * s.side;
  }
}
```

Lean 4:

```lean
inductive Shape where
  | circle (r : Float)
  | square (side : Float)

def area (s : Shape) : Float :=
  match s with
  | .circle r    => Float.pi * r * r
  | .square side => side * side
```

---

### 4. Recursive function (factorial on `bigint`)

TypeScript:

```typescript
function factorial(n: bigint): bigint {
  if (n <= 0n) return 1n;
  return n * factorial(n - 1n);
}
```

Lean 4:

```lean
def factorial (n : Int) : Int :=
  if n ≤ 0 then 1
  else n * factorial (n - 1)
termination_by n.toNat
```

---

### 5. Generic array map

TypeScript:

```typescript
function myMap<A, B>(arr: A[], f: (a: A) => B): B[] {
  return arr.map(f);
}
```

Lean 4:

```lean
def myMap {A B : Type} (arr : Array A) (f : A → B) : Array B :=
  arr.map f
```

---

## Invocation

```bash
.lake/build/bin/thales foo.ts            # runs foo.ts via the JS VM (subset-checked first)
.lake/build/bin/thales foo.ts        # type check + subset check + emit Foo.lean
.lake/build/bin/thales --no-emit foo.ts  # type check + subset check, no output file
```

`thales` and `thales` both enforce the Thales-TS subset when given a `.ts` file: subset violations emit `TH####` diagnostics and block execution. `thales` writes the shallow embedding to a sidecar `.lean` file by default; use `--no-emit` to skip that step.

## Known semantic divergences (0.5)

### String encoding: UTF-16 (JS) vs UTF-8 (Lean)

JavaScript strings are sequences of UTF-16 code units. Lean's `String` is a sequence of Unicode scalars (internally UTF-8). This produces observable differences for strings containing characters outside the Basic Multilingual Plane.

| Expression           | VM path (JS semantics)      | Lean path (emitted)      |
| -------------------- | --------------------------- | ------------------------ |
| `"😀".length`        | `2` (two UTF-16 code units) | `1` (one Unicode scalar) |
| `"ab".charCodeAt(0)` | `97`                        | unsupported in 0.5       |
| `"abc"[1]`           | `"b"`                       | `'b'` (Char, not String) |

0.5 posture: **accept the divergence and document it**. A future `TSString` wrapper preserving UTF-16 semantics is a 2 candidate. Programs using `.length` on strings that may contain non-BMP characters are not portable between the two paths.

### `NaN` equality

JS: `NaN === NaN` is `false`. Lean `Float`: `a == b` where `a` and `b` are both `NaN` also returns `false` (Lean `Float` delegates to IEEE 754). Consistent — no divergence — but users writing `x === NaN` checks should be redirected to `Number.isNaN(x)` (0.5 stdlib provides this).

### Object identity

JS: `{} === {}` is `false` (reference equality). The Lean image uses structural equality (`BEq`); `{} == {}` is `true`. Any Thales-TS program that relies on reference identity of objects (common in React / caching code) is out of the subset — but 0.5 doesn't detect this; it silently diverges. Flagged as a candidate for a future `TH####` check.

### Behavioral vs semantic equivalence

The example corpus verifies that the VM execution and the compiled Lean both produce the same output on the corpus inputs. This is _behavioral_ equivalence on a finite set of programs, not a proof of _semantic_ equivalence. A program not in the corpus that exercises an unhandled edge case can diverge silently between the two paths. A real semantic-equivalence theorem is 5 work.

## Built-in bounded number types (0.6)

`@thales/prelude` exports four built-in bounded number types: `Integer`, `Natural`, `Byte`, and `Bit`. On the TypeScript side each is a branded alias of `number`; on the Lean side each is a `Subtype` of `Float` (Lean's IEEE 754 double). The chain is:

```
Bit ⊆ Byte ⊆ Natural ⊆ Integer ⊆ number
```

- **`Integer`** — whole numbers in the range `[-(2^53 - 1), 2^53 - 1]` (JavaScript's safe-integer range).
- **`Natural`** — non-negative integers in `[0, 2^53 - 1]`.
- **`Byte`** — integers in `[0, 255]`.
- **`Bit`** — integers `0` or `1`.

### Widening and narrowing

The refinement types are subtypes of `number`, so every `Integer` (or `Natural`, `Byte`, `Bit`) is automatically a valid `number`. Going the other direction — from `number` to a refinement type — requires evidence, which comes in two forms:

**Predicate guards** (`isInteger`, `isNatural`, `isByte`, `isBit`): Boolean functions that narrow the type inside a conditional branch.

```typescript
import { isInteger } from '@thales/prelude';

function safeDouble(n: number): number {
  if (isInteger(n)) {
    return n * 2; // n: Integer here
  }
  return NaN;
}
```

**Throwing constructors** (`asInteger`, `asNatural`, `asByte`, `asBit`): Return the value typed as the refinement type, or throw `RangeError` if the value does not satisfy the predicate. Because these constructors may throw, programs that call them are not `@total` unless the compiler can see the value is already in range.

```typescript
import { asInteger } from '@thales/prelude';

const x: Integer = asInteger(42); // ok — 42 is a safe integer
const y: Integer = asInteger(3.14); // throws RangeError at runtime
```

**Literal shorthand**: Integer literals that fall within a type's range are accepted directly, without a constructor or guard.

```typescript
import { Integer } from '@thales/prelude';
const n: Integer = 7; // ok — 7 is a safe integer literal
const b: Byte = 200; // ok — 200 is in [0, 255]
```

Out-of-range literals are rejected with **TH0080**. Assigning a `number`-typed expression without evidence is rejected with **TH0081**.

### Arithmetic widens to `number`

Standard arithmetic operators (`+`, `-`, `*`, `/`, `%`, `**`) always produce `number`, even when both operands are refinement types. This matches JavaScript's runtime semantics — there is no Integer arithmetic ring in the type system. Users who need the result as a refinement type must apply a guard or constructor:

```typescript
import { Integer, isInteger } from '@thales/prelude';

declare const a: Integer;
declare const b: Integer;

const sum = a + b; // sum: number (arithmetic widens)
if (isInteger(sum)) {
  const s: Integer = sum; // ok — narrowed inside guard
}
```

### Naming clash warning

The prelude exports `isInteger` (tests for a safe integer). The global `Number.isInteger` tests the same mathematical property but is not part of the Thales subset and will produce a TS2339 error. Always import `isInteger` from `@thales/prelude`; do not call `Number.isInteger`.

### Stdlib overloads provided by the prelude

Three standard operations return refinement types when given appropriate arguments:

| Call                   | Return type | Notes                                                    |
| ---------------------- | ----------- | -------------------------------------------------------- |
| `Math.abs(n: Integer)` | `Natural`   | absolute value of a safe integer is always a natural     |
| `arr.length`           | `Natural`   | array length is always a non-negative safe integer       |
| `s.length`             | `Natural`   | string `.length` (UTF-16 code units) is always a natural |

These overloads are provided by `@thales/prelude`'s type declarations and require no import beyond the types themselves.

### Lean representation

Each refinement type is emitted as a Lean `Subtype`:

| TS type   | Lean type                                             |
| --------- | ----------------------------------------------------- |
| `Integer` | `{x : Float // x.isInteger && x.abs ≤ 2^53 - 1}`      |
| `Natural` | `{x : Float // x.isInteger && 0 ≤ x && x ≤ 2^53 - 1}` |
| `Byte`    | `{x : Float // x.isInteger && 0 ≤ x && x ≤ 255}`      |
| `Bit`     | `{x : Float // x = 0 ∨ x = 1}`                        |

Lean's kernel can check membership in these predicates for concrete literal values at compile time via `by decide`, so no `sorry` is introduced. The TH9004 post-emit check confirms that emitted files are sorry-free.
