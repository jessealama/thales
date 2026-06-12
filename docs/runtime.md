# Thales-TS Lean Runtime

Every Lean file emitted by `thales` begins with

```lean
import Thales.TS.Runtime
open Thales.TS
```

`Thales.TS.Runtime` is the Lean-side counterpart to the Thales-TS
surface stdlib. It supplies the handful of types and helpers the
emitter targets, chosen so that the Lean path's observable behavior
matches the JavaScript VM path byte-for-byte (see the runtime
byte-exactness clause in [`subset.md`](subset.md)). The runtime is
deliberately small — if a feature is not listed below, it is not in
the subset yet.

The source of truth is [`Thales/TS/Runtime.lean`](../Thales/TS/Runtime.lean);
this document describes the surface the emitter consumes.

## Module layout

- `namespace Thales.TS` — the main surface. Emitted code `open`s this,
  so bare names like `consoleLog`, `Result`, `RangeError` resolve here.
- `namespace Thales.TS.ArrayOps` — array combinators. The emitter
  references these by their fully-qualified names.

## Types

### `Option'`

```lean
abbrev Option' := Option
```

`T | null` and `T | undefined` in Thales-TS emit as `Option T`. The
alias exists so that emitted source can read `Option` without
colliding with any user-defined `Option` in scope; day-to-day it
behaves identically to Lean's built-in `Option`.

### `Result α β`

```lean
inductive Result (α β : Type) where
  | ok (value : α)
  | err (error : β)
```

Mirrors the Thales-TS surface `Result<T, E>` tagged union
`{ok: true, value: T} | {ok: false, error: E}`. The `.ok` / `.err`
constructors match the TS constructors `ok(value)` / `err(error)` from
the prelude. Accompanying combinators:

- `Result.map   : (α → γ) → Result α β → Result γ β`
- `Result.mapErr: (β → γ) → Result α β → Result α γ`
- `Result.andThen: (α → Result γ β) → Result α β → Result γ β`
- `Result.isOk  : Result α β → Bool`
- `Result.isErr : Result α β → Bool`

### Built-in error record types

```lean
structure Error         where message : String
structure TypeError     where message : String
structure RangeError    where message : String
structure SyntaxError   where message : String
structure ReferenceError where message : String
```

These are flat records (not a hierarchy — there is no subtyping from
`TypeError` to `Error`). A TS expression `new RangeError("msg")` emits
as `Thales.TS.RangeError.mk "msg"`. `@throws RangeError` functions
produce `Except RangeError T`, and catches pattern-match on the exact
record type declared in `@throws`.

## Functions

### `consoleLog` and the `JSShow` class

```lean
class JSShow (α : Type) where jsShow : α → String
def  consoleLog {α : Type} [JSShow α] (x : α) : IO Unit
```

Top-level `console.log(x)` in TS emits as `#eval consoleLog x` in
Lean. `JSShow` implements the small subset of JS `ToString` semantics
the v1 corpus exercises, so that stdout from `lake env lean` matches
stdout from the VM without post-processing:

| TS type                                  | Lean type | `JSShow` rendering                               |
| ---------------------------------------- | --------- | ------------------------------------------------ |
| `number`                                 | `Float`   | `jsNumberToString` (see below)                   |
| `bigint`                                 | `Int`     | decimal followed by `n` — e.g. `5n`, `-3n`, `0n` |
| `number` (non-negative integer contexts) | `Nat`     | plain decimal                                    |
| `string`                                 | `String`  | identity                                         |
| `boolean`                                | `Bool`    | `"true"` / `"false"`                             |

`jsNumberToString` implements the common cases of JS number
stringification: `NaN` prints as `"NaN"`, `0` as `"0"`, whole-valued
floats print without a decimal (`42.0 → "42"`), and fractional floats
strip trailing zeros (`12.560000 → "12.56"`). It does **not** yet
implement the exponential branch of ECMA-262 ToString — very small or
very large numbers fall through to Lean's `%f` formatting and may
diverge from V8's output. This is a known v1 limitation.

### Array indexing and combinators

```lean
def Thales.TS.indexRead (xs : Array α) (i : Float) : Option α
```

`arr[i]` in Thales-TS compiles under `noUncheckedIndexedAccess`, so it
returns `T | undefined`. The emitter lowers the indexing expression to
`Thales.TS.indexRead arr i`, which returns `Option T` in Lean. The index
stays a `Float` (TS `number`): fractional, negative, NaN, infinite, and
out-of-bounds indices all read as `undefined` (`none`), exactly as in JS.
(`Thales.TS.Array.get?`, the `Nat`-indexed variant, remains in the runtime
surface for hand-written Lean.)

Array methods live in `Thales.TS.ArrayOps` and are referenced by the
emitter via their qualified names:

```lean
ArrayOps.map    : Array α → (α → β) → Array β
ArrayOps.filter : Array α → (α → Bool) → Array α
ArrayOps.reduce : Array α → β → (β → α → β) → β
ArrayOps.concat : Array α → Array α → Array α
ArrayOps.length : Array α → Nat
ArrayOps.slice  : Array α → Nat → Nat → Array α
```

### Number parsing

```lean
def parseFloat (s : String) : Float
def isNaN      (x : Float)  : Bool
```

`parseFloat` accepts integer strings, optional-sign decimal strings,
and returns `NaN` (i.e. `0.0 / 0.0`) for unparseable input, matching
JS behavior on the cases the corpus exercises. It does not yet accept
scientific notation, leading whitespace, or hex/octal/binary prefixes.

## Emitted module shape

A minimal emitted file looks like:

```lean
import Thales.TS.Runtime

open Thales.TS

set_option linter.unusedVariables false

namespace Input

def greet (name : String) : String := s!"Hello, {name}"

#eval (consoleLog (greet "world"))

end Input
```

The `open Thales.TS` is what lets `consoleLog`, `Result`, and the
error records appear unqualified. `Thales.TS.ArrayOps.*` and
`Thales.TS.indexRead` remain fully qualified in the emitted source
because they intentionally do not live under the opened namespace.

## What the runtime does _not_ provide

The runtime is sized to v1 — anything outside this list is out of
scope for now and should be added alongside the TS surface feature
that requires it.

- No mutable containers, no `Map` / `Set`, no iterators.
- No `Promise` / async plumbing. Async is TH0012.
- No regex, no `Date`, no `Math.*` beyond what the emitter inlines.
- No class runtime. Classes are TH0030.
- No string stdlib beyond Lean's built-ins. `String.length` counts
  Unicode scalars in the emitted Lean, but UTF-16 code units in the VM
  path — see the divergence note in [`subset.md`](subset.md).
- `jsNumberToString` does not yet cover the exponential branch of
  ECMA-262 ToString. See [`future.md`](future.md) for planned work.
