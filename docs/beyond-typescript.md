# Beyond TypeScript

Thales accepts a strict subset of `tsc --strict`: every Thales program
is a TypeScript program, every TypeScript program Thales accepts means
the same thing under `tsc`'s rules. What Thales adds is a second layer
of meaning that TypeScript itself cannot express. This document
collects the four semantic enrichments and explains what each one
gives a user that TypeScript alone does not.

For the surface contract — what Thales accepts vs. rejects — see
[`subset.md`](subset.md). For the diagnostic catalogue, see
[`errors.md`](errors.md). This document focuses on _why_, not _what_.

## Typed exceptions: `@throws`

In TypeScript, a function's signature does not say which errors it can
throw. Callers see `() => User`; the throw is documentation at best,
silent surprise at worst.

Thales reads `@throws RangeError` (or any concrete error record) from
the JSDoc and lowers the function to `Except RangeError User` in the
emitted Lean. Catches in TypeScript become pattern matches on the
`Except` value. This means:

- The Lean type system enforces that callers either handle the failure
  or propagate it via their own `@throws`. There is no path that
  silently swallows.
- The `try`/`catch` body is type-checked as a continuation that may
  receive any of the declared error types — no broader, no narrower.

TypeScript can simulate some of this with `Result<T, E>`-style return
types, at the cost of rewriting every call site. Thales lets the
TypeScript code keep its native shape (`throw`, `try`/`catch`) and
extracts the typed-failure structure for downstream reasoning.

## Totality: `@total`

TypeScript has no termination checker. A function that recurses
forever is a runtime concern, not a type-level one.

`@total` declares a stronger contract than TypeScript can enforce:

1. The function terminates on every input. Lean's termination checker
   must accept it.
2. No failure can escape — no uncaught `throw`, no uncaught call into a
   `@throws` callee, no division by zero on a path the prover sees.

A `@total` function emits as a plain Lean `def` rather than the default
`partial def`. Downstream Lean code can therefore unfold it inside
proofs and reason about its return value as a total function of its
inputs.

`@total` and `@throws` are mutually exclusive: a `@total` function
asserts that no failure escapes, so it cannot also declare one
(TH0066).

## Refinement types that reflect into Lean's `Int` and `Nat`

This is the v0.6 headline. The prelude exports four refinement types —
`Integer`, `Natural`, `Byte`, `Bit` — which are aliases of `number` on
the TypeScript side and `Subtype`s of `Float` on the Lean side. The
Lean type carries a proof that the predicate holds; the proof field
erases at runtime so byte-identity with the TypeScript path is
preserved.

### What TypeScript users can do today, on their own

Several established TypeScript techniques look refinement-type-shaped:

- **Branded types.** `type Integer = number & { __integer: unique symbol }`
  gives a static-only nominal distinction. The brand is a phantom — the
  runtime value is just a `number`, and nothing in the type system
  derives consequences from "this number is integer-valued."
- **Runtime validators.** Libraries like `zod` and `io-ts` parse a
  `number` and produce a tagged success or error. The static type is
  refined, but the refinement is opaque to any reasoning beyond
  TypeScript itself.
- **User-defined type guards.** `function isInteger(x: number): x is Integer`
  gives narrowing, with the same opaque-brand caveat.

Each of these gives _static narrowing_, sometimes paired with _runtime
validation_. None of them gives the value any meaning beyond
"TypeScript believes this number satisfies a predicate." There is
nowhere to take the value where the predicate has consequences.

### What Thales adds

The Lean side of a Thales program treats `Integer` as
`{ x : Float // isInteger x = true }` — a real Subtype whose proof
field is part of the term. Two operators bridge to Lean's mathematical
integer types:

```lean
def Integer.toInt (x : Integer) : Int
def Natural.toNat (n : Natural) : Nat
```

Four homomorphism axioms (catalogued in [`axioms.md`](axioms.md))
state that arithmetic on `Integer`s commutes with arithmetic in `Int`,
within the safe-integer range:

```lean
axiom Integer.add_homomorphism (x y : Integer)
    (hsum : isInteger (x.val + y.val) = true) :
  Integer.toInt ⟨x.val + y.val, hsum⟩ = x.toInt + y.toInt
-- and analogous statements for sub, mul, plus toInt_ofInt round-trip
```

So a Thales function on `Integer`s, viewed from Lean, can be reasoned
about as if it were `Int` arithmetic. The proof you write to verify
some property of the function does not have to grovel through Float
representation issues for the cases the safe-integer predicate
guarantees away.

This is the property TypeScript-side refinement types cannot provide.
TypeScript has no proof system to reflect into, so even the most
elaborate brand or validator stops at the boundary of "the type
checker is convinced." Thales's prelude types continue past that
boundary into Lean, where downstream tooling can reason about them as
mathematical integers.

### Where the bridge bottoms out

The reflection is honest about its trust budget:

- It only holds within the safe-integer range. Operations whose result
  exceeds `2^53 - 1` widen to plain `number` and the user must narrow
  back via a guard or `as<T>` constructor.
- The four homomorphism axioms are postulated, not proven, because
  Lean's stdlib does not currently expose IEEE-754 exactness theorems
  on safe-integer inputs. See [`axioms.md`](axioms.md) for the full
  list and the rationale.
- Proofs about Thales programs ultimately rest on the IEEE-754
  properties summarized there. They are mechanical and stable, but
  they are postulates.

## Provably-safe array indexing

Lean's array access requires a proof that the index is in bounds.
TypeScript's access produces `T | undefined` under
`noUncheckedIndexedAccess` or unchecked `T` without — neither carries
the proof.

For two patterns where the in-bounds property is statically derivable,
Thales emits a proof-carrying access:

- **P1 — literal index into literal array.** `[10, 20, 30][1]` emits
  `arr[1]'(by native_decide)` and returns `T`, not `T | undefined`.
- **P2 — `Natural` index narrowed by length.** Inside
  `if (i < xs.length) { xs[i] }` where `i : Natural`, the access emits
  `xs[i.toNat]'h` with the bounds proof drawn from the surrounding
  `dite`-introduced hypothesis, the Subtype proof on `i`, and the
  `Float.toUInt64_of_isNatural` boundary axiom.

Other access patterns continue to emit `xs[i]?` and return `Option T`.
The relevant point: the safe sites round-trip through Lean as total
functions whose result is exactly what you asked for, not a fallback.

## Why this matters

A common framing of "compiles TypeScript to language X" is "we run on
X's runtime instead of V8." Thales is not that. Thales preserves
runtime equivalence with V8 — that is the byte-identity contract — and
spends its design budget on a different goal: producing a Lean module
that downstream proof tooling can reason about.

The four enrichments above are what give that downstream module its
proof surface:

- `@throws` makes failure modes visible to a `match`.
- `@total` makes the function unfoldable in proofs.
- Prelude refinement types let safe-integer arithmetic round-trip
  through `Int`/`Nat`.
- Provably-safe indexing eliminates `Option` from access sites where
  the in-bounds property is constructible.

None of these are reachable from TypeScript alone, no matter how
elaborate the brand or library. The boundary the user crosses, by
adopting Thales, is the boundary between "the type checker is
convinced" and "Lean can derive consequences." The strict-subset
promise on the TS side is what makes that crossing safe to write
inline, in normal TypeScript, without a separate proof file.
