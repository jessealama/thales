# Thales-TS Growth Path

## 0.5 (today)

Pure-functional subset with Lean source emission. Beta. See `subset.md`.

## 1.0 — production-ready 0.5

The same subset as 0.5 with broader example coverage, polish on diagnostic
line/column anchoring, and a stability commitment on the CLI surface and
the emitted-Lean format. The first release allowed to make compatibility
promises.

## 1.0.x — nullable usage-site gaps

Two spec'd usage-site translations for nullable types landed partially in
v1.0 but are not end-to-end working:

- **`??` nullish coalescing.** `x ?? y` is not narrowed by the type
  synthesiser: the result still has type `T | null` rather than `T`, so
  callers see a `TS2322` error. Fix is in `Thales/TypeCheck/Synth.lean`
  for the logical-expression with `operator = .nullishCoalesce`.
- **`?.` optional chaining.** The member-expression emitter at
  `Thales/Emit/Lean.lean:357` matches both optional and non-optional
  member access in the same case, so `u?.name` lowers as if it were
  `u.name` — which fails to elaborate against an `Option User`. Fix is a
  new case that emits `Option.map (·.field)` when the optional flag is
  set. Pairs with a fix for plain object-literal emission (non-discriminated
  records currently emit `(unsupported expr)`).

Neither gap blocks the three v1.0 headline features (Option via
`T | null` narrowing, `@throws` + Except, `@total`). Both are candidates
for a v1.0.1 patch.

## 1.1 — termination polish for `@total`

**What shipped in v1.0:** Functions annotated `@total` emit as `def` (not `partial def`); Lean's default structural-recursion checker must accept the function as-is. If it fails, TH0070 fires with Lean's error text. No `termination_by` or `decreasing_by` is emitted.

**What 1.1 adds:** A "grab bag" of tactics and measure templates so that more idiomatic recursive functions pass the termination checker without requiring the user to restructure.

**Toolkit additions for 1.1:**

*(a) Measure templates emitted as `termination_by` clauses:*
- `termination_by n.toNat` — `bigint`/`Int` functions with a clear non-negative decrease
- `termination_by arr.size - i` — index-counting recursion
- `termination_by xs.size` — array recursion via `.slice(1)` etc.
- Lexicographic `termination_by (a, b)` — mutual or nested counters

*(b) A `thales_decrease` tactic macro bundling the common discharge sequence* (`simp_wf; omega`, then `decide`, then fallback). Emitted as the `decreasing_by` clause.

*(c) Pattern-based type refinement:* when a parameter is used as a non-negative counter (base case `=== 0`, recursive call on `n - 1`), the emitter offers to narrow its Lean signature from `Int` to `Nat`. Opt-in via a `@nat` JSDoc hint in 1.1, possibly inferred in later releases.

*(d) Explicit precondition hoisting:* a TS runtime guard like `if (n < 0n) throw new Error(...)` hoists `n ≥ 0` into the Lean function's signature. Pairs with 4's `@requires`.

*(e) Fuel-based escape:* for functions no static measure captures, rewrite to take an explicit `fuel: nat` parameter whose decrease is trivial. An alternative to removing `@total` that keeps induction working.

**Explicit targets for 1.1 acceptance:** the canonical `fact` on `bigint` and a `fibonacci` variant should compile cleanly under `@total` using (a) + (b) at minimum.

**Scope:** 1.1 is the smallest release that turns v1.0's "structural recursion only" baseline into a usable `@total` annotation for idiomatic TS. It lands before 1.5 (mutation) because it unlocks more of TS without introducing monadic translation.

## 1.5 — local mutation via Id.run do

**New surface:** `let x = 0; x = 1;` accepted. `for (let i = 0; i < arr.length; i++) { ... }` accepted. `arr.push(x)` on locally-constructed arrays accepted. Mutation of function parameters still rejected (would require escape analysis).

**Translation:** Function bodies containing mutation switch from direct shallow embedding to `Id.run do` with `mut` bindings. For loops become `for ... in ...` blocks. `arr.push(x)` rebinds `arr := arr.push x`.

**Proof story:** Mathlib `mvcgen` generates verification conditions for `Id.run do` blocks. Users prove loop invariants via `@invariant` JSDoc tags (introduced here).

**New TH####:** TH0001-TH0005 become warnings/relaxations when the containing function opts into `Id.run do` style. TH0050 still applies to non-terminating recursion.

## 2 — classes without inheritance

**New surface:** `class Point { x: number; y: number; distance(other: Point): number { ... } }`. Instance methods accepted. Static methods accepted. Getters/setters accepted (translate to methods). `private` translates to "not exported from the Lean namespace."

**Translation:** `class C { ... }` becomes Lean `structure C where ...` plus `def C.methodName (self : C) ...`. No inheritance, no `this`-rebinding, no `instanceof`.

**Not yet:** `extends`, decorators, `abstract`, `protected`.

## 3 — typed exceptions

**New surface:** `throws E` annotation in function signatures. `throw new E(...)`. `try { ... } catch (e: E) { ... }`. Standard `Error` subclasses.

**Translation:** Functions with `throws` translate to `Except E`. `throw` becomes `Except.error`. `try/catch` becomes a pattern match on the `Except` value.

## 4 — proof annotations

**New surface:** JSDoc tags `@requires`, `@ensures`, `@invariant`, `@decreasing`, `@proof`, `@partial`. Parsed from doc comments. Translated to Lean preconditions/postconditions/invariants. Inline `@proof` blocks contain Lean tactic text.

**Discharge order:** `decide` → `simp` with Thales-provided simp set → user-supplied `@proof` tactic block → leave as open obligation.

## 5+ — equivalence with the VM path (long-term research)

**Thesis:** For every Thales-TS program P in the subset, the VM's execution of `erase(P)` equals the result of compiling and running `emitLean(P)`.

**Approach:** Build a Lean theorem connecting the operational semantics of the VM bytecode to the shallow embedding. A research program, not an engineering task.

**Status:** Deferred indefinitely. The v1.0 example corpus demonstrates *behavioral* equivalence on a specific set of programs. This is a sanity check, not a soundness proof. Counterexamples may exist outside the corpus (the string-encoding divergence documented in `subset.md` is one such example). Do not read v1.0 as claiming semantic equivalence.

## 6+ — single inheritance, async, refinement types, wider stdlib

Defer until 1–5 are proven on real workloads.
