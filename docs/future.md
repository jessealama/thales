# Thales-TS Growth Path

There are two "story arcs" for Thales:

1. close the gap with how TS programmers actually write code, and
2. add the verification work that justifies a Lean sidecar in the first place.

## Arc 1: Meet TypeScript halfway

Real TS code does local mutation, uses classes extensively,
does stateful iteration, and async without ceremony. These
features are currently not supported by Thales. Closing that
gap would mean:

- **Local mutation via `Id.run do`.** Accept reassignment,
  `for` loops, and `arr.push` on locally-constructed
  arrays. Function bodies that mutate switch from direct
  shallow embedding to `Id.run do` with `mut`
  bindings. Mutation of parameters and captured variables
  stays out, for now.

- **Classes with single inheritance.** Instance and static
  methods, getters, setters, `extends`, method override,
  `super`. `class C` becomes Lean `structure C`; `class D
extends C` becomes `structure D extends C`, with a
  closures-as-fields encoding for the cases that need
  polymorphic dispatch through a base-class parameter.

- **Generators.** `function* gen() { yield x; … }`
  translated to a Lean `Stream` (or perhaps `List` when
  bounds are known). Restricted to clean coalgebraic cases:
  no two-way communication via `.next(value)`, no `yield*`
  delegation, no bidirectional generators.

- **async/await.** Modelled as `IO` (or a tailored `Async`/`Task`
  monad), with `await` lowering to monadic bind. This captures the
  type discipline of async TS but not faithful event-loop semantics,
  microtask ordering, or cancellation — same modelling philosophy as
  `@throws`.

## Arc 2: Bring proofs to TypeScript

Once the subset is wide enough for realistic programs, we're
going to build out program verification for TypeScript.

- **Proof annotations.** Support basic function and
  method-level verification conditions via` @requires`,
  `@ensures`, loop invariants via `@invariant`, translated
  to Lean preconditions, postconditions, loop invariants,
  and inline tactic blocks. TS runtime guards like `if (n <
0n) throw new RangeError(…)` hoist into compile-time
  obligations.

- **Refinement types.** A predicate-subtype layer on the
  proof-annotation machinery: `/** @refine x => x > 0 */
type PosInt = number;` becomes a subtype in Lean. Function
  signatures that take or return refined values introduce
  obligations at the call site, discharged by the same
  pipeline. Encodes non-empty arrays, in-range indices,
  sorted lists, validated strings without hand-rolling a
  runtime guard for each.

## Interaction of the arcs

The arcs don't constitute a roadmap with distinct version
numbers. We intend that the arcs build off of each other: a
bit of progress in one, a bit of progress in the other,
going back and forth.

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
