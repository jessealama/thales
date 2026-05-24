# Changelog

All notable changes to Thales are recorded here. The README and the
`docs/` tree are the source of documentation; this file only tracks
release-to-release deltas. The format follows
[Keep a Changelog 1.1.0](https://keepachangelog.com/en/1.1.0/).

## Unreleased

Rough plans for 0.8.

### Added

- forEach-callback bounds: `arr.forEach((x, i) => arr[i])` becomes a
  provably-total access. 0.6 already types the callback's `index`
  parameter as `Natural`; the bounds-aware emit lowering is the next
  step.
- TH0081 in more positions: object-literal properties, array elements,
  generic arguments, rest parameters, spread elements, default values,
  and property initializers. 0.6 emits TH0081 only at variable
  declarations, function parameters, and return statements.
- Tuple indexing as a provably-total access: `tup[k]` for tuples with
  statically-known length returns `T` instead of `T | undefined`.
- Top-level `if`-statements in script files. 0.6 only lowers top-level
  declarations and bare expressions; ifs at the top level currently
  must be wrapped in a function.

## 0.7 — forthcoming

Provably-safe array indexing in two contexts: literal-index into a
literal array (`[10, 20, 30][1]`) and length-narrowed access with a
`Natural` index (`if (i < xs.length) xs[i]` where `i: Natural`). These
will return `T` instead of `T | undefined`. The Lean-side soundness
basis is a seventh boundary axiom (`Float.toUInt64_of_isNatural`) plus
`Natural.toNat`, which round-trip an `isNatural` Float through
`UInt64.toNat` for use as a `Nat`-typed index.

## 0.6 — 2026-05-24

### Added

- `@thales/prelude` module exporting four built-in bounded number
  types: `Integer` (safe integer), `Natural` (non-negative safe
  integer), `Byte` (`0..255`), and `Bit` (`0` or `1`). The chain
  `Bit ⊆ Byte ⊆ Natural ⊆ Integer ⊆ number` is enforced at compile
  time.
- Eight prelude functions per refinement type:
  `isInteger`/`isNatural`/`isByte`/`isBit` (TypeScript type-guard
  predicates) and `asInteger`/`asNatural`/`asByte`/`asBit` (throwing
  constructors that raise `RangeError` on out-of-range input). At the
  top level, a bare `asBit(2);` statement is emitted as an
  `asBitEffect` IO mirror that `IO.Process.exit 1`s on failure so the
  Lean path matches `tsx`'s nonzero exit.
- Predicate-guard narrowing: `if (isInteger(x)) { ... }` (also
  `Number.isSafeInteger`) narrows `x` to the corresponding refinement
  type in the true branch. `Number.isInteger` is intentionally not
  recognized — it admits unsafe integers.
- TH0080: numeric literal out of range for a refinement type (e.g.,
  `const c: Byte = 256`).
- TH0081: a `number`-typed value is not assignable to a refinement slot
  without narrowing or constructor evidence (variable declarations,
  function parameters, return statements).
- TH9004: emitted Lean code contains `sorry`. The conformance harness
  greps every emitted file after emit and fails on a hit.
- Lean-side reflection for `Integer`: `Integer.toInt` and
  `Integer.ofInt` round-trip the type into `Int`, with arithmetic
  homomorphisms for `+`/`-`/`*`. Downstream Lean proofs can reason
  about safe-integer arithmetic at the `Int` level.
- Twelve IEEE-754 boundary axioms in `Thales.TS.Runtime`, grouped by
  purpose (Float ↔ Int boundary, `Float.abs`, `Integer` reflection).
  See [`docs/axioms.md`](docs/axioms.md) for the full list and
  rationale. `JSShow` instances for the four refinement types so
  `console.log(x)` prints them the same way as the VM path.
- [`docs/beyond-typescript.md`](docs/beyond-typescript.md): an
  orientation for readers who want to know what Thales gives you that
  TypeScript alone cannot — the bounded number types are the v0.6
  headline.

### Changed

- `Math.abs` is typed `Integer → Natural` when the argument is
  `Integer`-typed (still `number → number` otherwise). The Lean
  runtime ships `Math.absI : Integer → Natural` for this overload.
- `Array<T>.length` and `string.length` are typed `Natural` (was
  `number`). Existing code that assigned them to `number` continues to
  work via the chain's coercions.
- `Array<T>` callback types for `forEach`, `map`, `filter`, and
  `reduce` give the `index` parameter type `Natural` (was `number`).
- Conformance corpus relocated from `examples/` to
  `tests/conformance/{accept,reject,throws,future}`. Contributors
  adding fixtures should pick the directory that matches the fixture's
  expected outcome; `future/` holds parked fixtures the harness
  ignores.

### Fixed

- Conformance harness now passes `NODE_OPTIONS=--disable-warning=DEP0205`
  to its `tsx` invocation. tsx triggers Node's deprecated
  `module.register()` API once per process; the resulting stderr line
  was failing byte-identity checks on every fixture.

## 0.5 — 2026-04-28

Initial release.
