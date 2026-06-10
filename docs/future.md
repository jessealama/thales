# Thales-TS Growth Path

There are two "story arcs" for Thales:

1. close the gap with how TS programmers actually write code, and
2. add the verification work that justifies a Lean sidecar in the first place.

The arcs build off each other — a bit of progress in one, a bit in the
other — rather than forming a roadmap with distinct version numbers.
What follows is the canonical statement of where Thales is going; when
direction changes, this document changes with it.

## Arc 1: Meet TypeScript halfway

Real TS code does local mutation, uses classes extensively, does
stateful iteration, and async without ceremony.

### Active now: mutation, loops, stdlib (June 2026)

The current slate, tracked in issues
[#23](https://github.com/jessealama/thales/issues/23)–[#29](https://github.com/jessealama/thales/issues/29),
widens the executable subset in dependency order:

1. **Local variable mutation** — reassignment, `++`/`--`, the `+=`
   family on non-escaping locals, emitted as `Id.run do` with `let mut`
   bindings. Mutation of parameters and captured variables stays out
   until a concrete pattern demands an escape (then: `StateM`, or a
   fuller heap model).
2. **`for` / `for-of`** — `for x in arr do`; lands before `while`
   because folds over finite structures keep totality available.
3. **`while` / `do-while`** — Lean's do-notation `while`, which is
   backed by a `partial` combinator: fine for evaluation (the
   byte-match contract is unaffected), opaque to proofs. `@total` and
   `while` are therefore mutually exclusive, mirroring the
   `@throws`/`@total` design. Verification of while-bodies arrives
   later via loop invariants (see Arc 2).
4. **Local array mutation** — `.push`/`.pop`/element assignment on
   non-escaping `let` locals.
5. **Stdlib breadth** — array methods (`join`, `indexOf`, `includes`,
   …), `padStart`/`padEnd`, `Number.*`/`Math.*` gaps, one method at a
   time.

Progress is measured against per-feature **test262** directory slices
(pass rate within the declared subset), with **left-pad** — ported to
`tsc --strict`, compiled whole, byte-exact — as the end-to-end target.

### Later in Arc 1

- **Classes with single inheritance.** Instance and static methods,
  getters, setters, `extends`, method override, `super`. `class C`
  becomes Lean `structure C`; `class D extends C` becomes `structure D
  extends C`, with a closures-as-fields encoding for the cases that
  need polymorphic dispatch through a base-class parameter.

- **Generators.** `function* gen() { yield x; … }` translated to a Lean
  `Stream` (or perhaps `List` when bounds are known). Restricted to
  clean coalgebraic cases: no two-way communication via `.next(value)`,
  no `yield*` delegation, no bidirectional generators.

- **async/await.** Modelled as `IO` (or a tailored `Async`/`Task`
  monad), with `await` lowering to monadic bind. This captures the type
  discipline of async TS but not faithful event-loop semantics,
  microtask ordering, or cancellation — same modelling philosophy as
  `@throws`.

## Arc 2: Bring proofs to TypeScript

This is the destination: Thales as a **verification layer over
TypeScript**. Source files stay valid `tsc --strict` TypeScript;
Thales-specific meaning rides on JSDoc tags, so the rest of the
ecosystem (bundlers, editors, linters) sees ordinary TS.

- **Refinement types.** The first installment shipped in 0.6: the
  `@thales/prelude` bounded numerics (`Integer`, `Natural`, `Byte`,
  `Bit`) with compile-time-enforced subtyping and guard/constructor
  functions. The next layer is user-defined refinements — `/** @refine
  x => x > 0 */ type PosInt = number;` becomes a subtype in Lean, with
  call-site obligations discharged by the same pipeline. Encodes
  non-empty arrays, in-range indices, sorted lists, validated strings
  without hand-rolling a runtime guard for each.

- **Executable specifications.** `@requires`/`@ensures` on functions
  and properties stated as ordinary boolean-returning TS functions,
  with **dual discharge**: every spec can be run as a generated
  property-based test (fast-check), and specs you want *proved* rather
  than tested escalate to Lean, where a single curated tactic attempts
  the proof automatically. No manual proof syntax to start — when the
  automation fails, the user gets a counterexample (when one exists)
  and refactors or weakens the spec.

- **Loop invariants.** `@invariant` on `while`/`for-of` closes the loop
  (literally) between the arcs: the imperative subset from Arc 1
  becomes verifiable via verification-condition generation over the
  monadic emission, following Lean's `mvcgen` machinery as it matures.

## Emit architecture: structured output instead of strings

This is a robustness follow-on, not part of either feature arc.

Today the emitter (`Thales/Emit/LeanSyntax.lean`) builds Lean source by
rendering a custom `LExpr` AST to **strings** and concatenating them,
with newlines. Correct **parenthesization** and **layout** are
unenforced invariants maintained by hand — `renderExprAtom` wraps
non-atomic forms, `indent` re-indents every line. That kind of invariant
leaks. We have already hit two instances:

- A top-level `if` branch that sequenced IO (a `console.log`) **and** a
  nested narrowing `if` emitted a `do` block whose nested `let … else …`
  chain was not grouped, orphaning the trailing `else` (Lean: `unexpected
token 'else'`). Fixed by atomizing `doSeq` elements, but the fix is
  "remember to group at this new context" — the same shape of latent bug
  can reappear at the next layout-sensitive context.
- A bare `number` flowing into an `Option`-typed slot emits the
  unwrapped value, which is a different category (missing `.some`
  injection) but the same theme: string emit makes whole classes of
  malformed output expressible.

Lean has the machinery to make these impossible by construction. The
idea: emit a **structured representation** that gets serialized, rather
than assembling text. Two variants, both larger than any per-bug patch:

- **A — Lean's own syntax + pretty-printer.** Build `Lean.Syntax` /
  `TSyntax` (directly or via quotation) and serialize with
  `Lean.PrettyPrinter`: the **parenthesizer** inserts parentheses where
  the grammar requires them (by precedence), and the **formatter** lays
  out via `Std.Format` (`nest`/`group`/`align`, a Wadler-style engine).
  Parenthesization and indentation become correct by construction.
  _Cost:_ the printer runs in `CoreM` and needs an `Environment` with the
  relevant notations imported, so emit would stand up a Lean elaborator
  context (`importModules` + run) instead of doing pure string work; it
  couples emit to Lean's internal pretty-printer API, which moves across
  toolchains (a maintenance cost against the pinned toolchain and future
  bumps); and it is a rewrite of `LeanSyntax.lean`. The conformance
  contract is on program **stdout**, not `.lean` source, so byte-identity
  is unaffected — but any `Test/Emit` expectations that match emitted
  source text would need regenerating against a fixed print width.

- **B — keep `LExpr`, replace the renderer.** Swap the string renderer
  for a `Std.Format`-based one (correct indentation via `nest`/`group`)
  plus a precedence-aware parenthesization pass over `LExpr`. Kills the
  same bug class with no `CoreM`/`Environment` dependency and a smaller
  blast radius, at the cost of re-implementing precedence rules ourselves
  rather than inheriting Lean's.

Neither is scheduled. The trigger to pick this up is a third instance of
the bug class, or any larger emit expansion (e.g. classes, generators)
that would multiply the number of layout-sensitive contexts we maintain
by hand.

## Non-goals

We do not aim for Thales to ever match _all_ of
TypeScript. That's just too big. Although I want Thales to
be useful for "real" TypeScript, the overall goal is to make
Lean-backed program verification for TypeScript a reality;
full fidelity to TypeScript isn't what we're after. Some
features strike us as a bit too heavyweight and difficult to
model in Lean, as of today. We will probably not work on
these in the near future (and as we progress on Arc 1, we
will probably add more items to this list):

- **Decorators.** Used for a kind of metaprogramming in
  TypeScript. This is conceptually very attractive! But it's
  hard to model faithfully in Lean.

* **Mixins.** Faithful modelling seems awkward in Lean.

This list isn't written in stone! As Lean grows, and as our
knowledge of Lean and TypeScript grows (it's always growing,
thanks to Thales!) it's conceivable that some features might
get _removed_ from this list and moved to Arc 1. (But then
again, they might move from Arc 1 back to this list!)
