# Basic Refinement Types — Master Spec for Thales 0.6 → 0.9

**Status:** Design largely locked, implementation pending. Roadmap
revised 2026-05-06 to span four versions (0.6 → 0.9), each shippable
as workable software with visible user value. Single source of truth
for all refinement-types ideation.

> **⚠️ Version labels superseded (2026-05-26).** The actual release train
> diverged from the "0.6 → 0.9" ladder below. 0.6 shipped the built-in
> bounded number types (the "documentation primitives" milestone); **0.7
> became a 0.6-completeness release** (map/reduce inference, TH0081
> coverage, top-level `if` — see ADR-0002), **not** the "refinement-aware
> arithmetic + narrowing" described here. The refinement-arithmetic,
> verification-pipeline, and user-defined-refinement work in this spec is
> re-deferred and not yet scheduled (the framework as a whole is tracked as
> ~0.9 in `CONTEXT.md`). Treat every per-version milestone label in this
> document as historical design intent, not a committed schedule — the
> design content itself remains a valid reference.

**Target releases.** The feature lands across four versions, each
independently useful:

- **0.6** — refinement types as documentation primitives. Signatures,
  literal-range checks, stdlib overloads. No arithmetic enforcement,
  no narrowing, no verification.
- **0.7** — refinement-aware arithmetic + narrowing. Static sound
  table, mixed-pair extension, prelude guards, boundary pattern.
  Still no verification phase.
- **0.8** — verification pipeline. Real obligations, `thales_grind`,
  the L3 Float→Int reflection.
- **0.9** — user-defined refinements. The predicate-sublanguage
  parser; users write their own `@refine` aliases.

The dependency graph and milestone breakdown is in **Part VII**.

**Origin:** Arc 2 of the Thales roadmap (`docs/future.md`),
specifically the "refinement types" item. The framing question was
whether to ship a one-off `Integer` feature or to build the canonical
first slice of the refinement-type framework. We chose the framework
approach: ship a narrow but principled refinement system with
`Integer`, `Nat`, `Byte`, `Bit` as its first inhabitants — laddered
across four versions so each ships independently.

**Companion artifacts.**
- PoC: `Test/PoC/RefinementGrind.lean` and `Test/PoC/FINDINGS.md` on
  branch `feat/thales-grind-poc` (validates the 0.8 verification
  approach before any 0.6 code lands).
- GitHub milestone snapshot:
  https://github.com/jessealama/thales/milestone/1 (was a
  single-version snapshot; will be re-issued per-version from this
  spec when work is ready to start).

---

## How to read this doc

This is a long document because it bundles every working artifact for
the 0.6 → 0.9 ladder in one place. The sections progress from "what"
→ "why" → "how" → "in what order":

- **Part I — Locked design decisions.** The 16 decisions that
  define what "refinement types in 0.6" *is*. Stable; changes here
  invalidate downstream parts.
- **Part II — Decisions added during 2026-05-06 review.** Smaller
  follow-ups raised by external review, PoC findings, and a
  codebase audit. Each is now-resolved and lives here as the
  rationale of record.
- **Part III — Soundness & trust base.** The audit-ready story for
  the verification phase. Self-contained; can be read without the
  other parts.
- **Part IV — Corpus examples.** The nine `.ts` files that ship
  with 0.6 and define the contract operationally.
- **Part V — Source-map tracers.** Four data-flow walkthroughs
  used as a thinking tool for the verifier-pipeline design.
- **Part VI — PoC outcomes.** Validation evidence from the
  `feat/thales-grind-poc` branch.
- **Part VII — Version ladder & milestone breakdown.** The
  implementation plan, four versions, with working TS examples
  showing what each version makes possible.
- **Part VIII — Codebase audit.** Pre-conditions in the current
  code that the roadmap depends on.
- **Part IX — Out of scope.** The lock list, broken out per
  version.
- **Part X — Open questions.** What's still genuinely unsettled.
- **Part XI — Prelude documentation conventions.** How
  `Prelude.d.ts` carries both type aliases and refinement-aware
  overloads as the source of truth for what the prelude offers.
- **Appendix A — Documentation file changes per version.**
- **Appendix B — Glossary.**

A reader who only wants to understand the user-visible feature can
read Parts I, IV, VII (skim), IX. A reader auditing soundness reads
Part III. A reader executing the work reads Parts VII, VIII, XI.
A reader thinking about how to extend the prelude reads Part XI.

---

## Part I — Locked design decisions

### 1. Framing: refinement-type framework, `Integer` as first instance

Build the smallest end-to-end slice of a general refinement-type
framework. `Integer`, `Nat`, `Byte`, `Bit` ship as inhabitants of
that framework, not as bespoke features. `@thales-type integer`
(originally proposed) is rejected in favor of the `@refine` syntax
already promised in `docs/future.md`.

### 2. Lowering: two-layered (L3)

- **Runtime:** A refinement-typed value lowers to its base TS type's
  runtime representation. `Integer` lowers to Lean `Float`. The
  refinement is *transparent at runtime* — that's the cultural
  promise of refinement types.
- **Verification:** For verification, the framework reflects refined
  values to a domain `omega` is strong on (Lean `Int` for the
  integer refinements). Boundary lemmas
  (`Float.IsSafeInteger x → ∃ n : Int, x = Float.ofInt n ∧ ...`)
  bridge the two layers.
- **Why:** Conformance byte-match is automatic (runtime is
  unchanged). `omega` operates on `Int`, where it is reliable.
  Future refinements (`NonEmptyArray`, `Email`, `InRange`) keep
  their runtime representations unchanged, which is essential.
- **Rejected alternatives:**
  - **(L1)** lowering `Integer` to Lean `Int` directly — sneaks
    semantic changes into `Integer / Integer` and breaks the
    refinement cultural promise.
  - **(L2)** `Float` subtype with proofs over `Float` — `omega`
    chokes because Lean `Float` is non-associative; PoC
    confirmed (see Part VI).

### 3. Surface syntax: `@refine` on type aliases (S2)

```ts
/** @refine x => Number.isInteger(x) */
type Integer = number;
```

- The base TS type (RHS of the alias) is what `tsc` sees, so `tsc`
  accepts the file as if `Integer` were just `number`.
- The JSDoc `@refine` directive carries the predicate.
- The predicate is written as JS-shaped syntax for familiarity, but
  in 0.6 it is interpreted only at compile time by Thales (matched
  against the predicate sublanguage in decision 5). Thales does
  not emit a runtime check from `@refine`; runtime validation is a
  separate concern with its own libraries (Zod and similar) and is
  not in scope here.
- **Rejected alternatives:**
  - **(S1)** hard-coded `Integer` in the type-checker — doesn't
    generalize.
  - **(S3)** JSDoc-on-variable — refinement-as-property-of-types
    is essential for cross-function reasoning.
  - **(S4)** TS branded types — branded `number & {__brand}` is
    not assignable to `number`.

### 4. Composition: subtype-aware refinement of refinements (P3)

`@refine` aliases may have *another refined alias* on the RHS. The
effective predicate is the conjunction along the chain. Subtyping is
read off the alias chain — no implication-checking obligations.

```ts
/** @refine x => Number.isInteger(x) */
type Integer = number;

/** @refine x => x >= 0 */
type Nat = Integer;          // effective: isInteger(x) ∧ x ≥ 0

/** @refine x => x <= 255 */
type Byte = Nat;             // effective: isInteger(x) ∧ x ≥ 0 ∧ x ≤ 255

/** @refine x => x < 2 */
type Bit = Nat;              // effective: isInteger(x) ∧ x ≥ 0 ∧ x < 2
```

These four types ship in `Thales/TS/Prelude.d.ts` as part of 0.6.

### 5. Predicate sublanguage

Final grammar (incorporates decision 9's named-constant extension):

```
predicate  ::= IDENT "=>" body
body       ::= atom ("&&" atom)*
atom       ::= "Number.isInteger(" IDENT ")"
             | IDENT cmp atom_value
             | atom_value cmp IDENT
atom_value ::= INT_LIT
             | "Number.MIN_SAFE_INTEGER"
             | "Number.MAX_SAFE_INTEGER"
cmp        ::= ">" | ">=" | "<" | "<="
INT_LIT    ::= ["-"] DIGIT+
```

The bound variable name is normalized internally (any identifier
allowed as the lambda parameter; same identifier must appear in
atoms).

- **No `||`, no `!`, no user function calls.** Future versions may
  add disjunction; negation is excluded because `&&` + `!` admits
  disjunction by De Morgan, breaking the bounded-tactic invariant.
- The base type of a `@refine` alias must be `number` or another
  refined alias.
- **Every atom must reference only the lambda's bound variable.**
  Free variables are forbidden: `x => x > 0 && y > 0` is rejected
  with `TH0087` ("Refinement predicate references variable not
  bound by the lambda parameter"). Naively translating such a
  predicate to Lean would produce an `unknown identifier` error in
  the verifier; Thales catches the issue earlier with a
  TS-positioned diagnostic pointing at the offending atom.
  Per-atom check at parse time; trivial to implement.
- Anything outside this grammar produces `TH0081` ("Refinement
  predicate not recognized").

### 6. Arithmetic propagation: refinements widen by default; small sound-by-construction static table

**Reframing.** `Integer` and `Nat` (with safe-integer bounds, see
decision 8) are *boundary refinements*. They carry information
across function signatures and through narrowing; they are *not*
arithmetic rings. Arithmetic on full-range `Integer × Integer` is
genuinely *not* closed under the safe-integer predicate:

- `MAX_SAFE_INTEGER + 1 = 2^53` is integer-valued but outside the
  safe bound, so the `Integer` predicate fails.
- `MAX_SAFE + MAX_SAFE` (each operand at the boundary) overflows
  Float precision such that the Float result and the Int reflection
  of the exact sum *disagree*, breaking L3 fidelity.
- `Nat ** Nat` runs to `Infinity` quickly; `Number.isInteger(Infinity)`
  is `false`.

Therefore the default is: **arithmetic widens to `number`; the user
re-narrows at the slot, or proves a bound via the obligation
pipeline.** Only a handful of operator-and-operand combinations are
provably refinement-preserving from the safe-integer bounds alone,
and those go on a small static table.

**Default widening.** All binary `+`, `-`, `*`, `**`, `/`, `%` on
two refined-int operands produce `number` unless they appear in the
static table below. When a `number` value flows into a refined
slot, an obligation is generated and the verifier (currently
`omega` over `Int` via L3 reflection) attempts to discharge it. If
it cannot, the user gets a refinement-violation diagnostic
(`TH0080`).

**Static sound-by-construction table.** A small set of forms whose
soundness is provable from safe-integer bounds and L3 reflection
alone; the type-checker applies these *without* generating an
obligation:

| Form                  | Result    | Why sound                                        |
| --------------------- | --------- | ------------------------------------------------ |
| Unary `-` on `Integer`| `Integer` | `\|MIN_SAFE\| = MAX_SAFE`, so negation stays in range |
| Unary `-` on `Nat`    | `Integer` | Result in `[-MAX_SAFE, 0]` ⊂ Integer             |
| `Bit & Bit`           | `Bit`     | Closed in `{0,1}`                                |
| `Bit \| Bit`          | `Bit`     | Same                                             |
| `Bit ^ Bit`           | `Bit`     | Same                                             |
| `Bit * Bit`           | `Bit`     | Same                                             |
| `Bit + Bit`           | `Nat`     | Result in `{0,1,2}`                              |
| `Byte + Byte`         | `Nat`     | Max `510 < MAX_SAFE`; Float-exact at this magnitude |
| `Byte * Byte`         | `Nat`     | Max `65025 < MAX_SAFE`; Float-exact              |
| `Byte - Byte`         | `Integer` | Range `[-255, 255]`; Float-exact                 |
| `Math.abs(Integer)`   | `Nat`     | `\|MIN_SAFE\| = MAX_SAFE` (decision 11)          |
| `Math.abs(Nat)`       | `Nat`     | Identity in range                                |
| `Math.abs(Byte)`      | `Byte`    | Same magnitude domain, refinement preserved      |
| `Math.abs(Bit)`       | `Bit`     | Same                                             |

The four `Math.abs` rows are covered by the more general
"`Math.abs` preserves any non-negative refinement" principle that
will generalize in post-0.6 work; they are spelled out individually
here for clarity.

**Mixed-refinement extension** is in Part II, decision D17.

**Notable omissions from the table.**

- **`Integer + Integer`, `Integer - Integer`, `Integer * Integer`,
  `Nat + Nat`, `Nat * Nat`, `Nat ** Nat`** — none of these are
  closed under the safe-integer predicate; obligations would
  correctly fail for some operands in range. The sound thing for
  users is to widen parameters to a smaller refinement (`Byte`) or
  accept widening to `number`.
- **`Integer % Integer`** — `5 % 0 = NaN`;
  `Number.isInteger(NaN)` is `false`. Closure requires the divisor
  be provably nonzero, which is not free. Widens to `number`; the
  user narrows after a `b !== 0` guard if needed.
- **`Integer / Integer`** — already widens (JS `5 / 2 = 2.5`).
  `Math.floor(a / b)` does *not* recover an `Integer`
  automatically because `Math.floor` returns `number` (NaN/Infinity
  for non-finite input — see decision 11 deferred list).

**Implication for the corpus.** The first instinct
— `function add(a: Integer, b: Integer): Integer { return a + b; }`
— is *correctly* rejected. The corpus shows this as an
expected-failure example so users see the boundary explicitly.

**Informational widening diagnostic (`TH0086`).** When binary
arithmetic on refined-int operands produces a `number` result
(i.e., widens), Thales emits an *informational* diagnostic at the
operator site:

> `TH0086`: arithmetic on `Integer`/`Nat`/`Byte`/`Bit` widens to
> `number`; the result may be out of refinement range without
> further assumptions.

This is a hint, not a build failure (severity *info*; see decision
12). The triggering rule for 0.6 is conservative: fire only when
*both* operands are refined-int and the operator/operand-types pair
is *not* on the static sound table. Forms that *are* on the table
do not fire `TH0086`.

For TH0086's interaction with `TH0080`, see Part II, decision D18.

### 7. Verification pipeline: dedicated verification phase (V3)

A new pipeline phase, structurally parallel to the `@total` totality
check, sits in `Thales/Main.lean` between subset checking and
directive application:

1. Parse
2. Type-check
3. `@throws` / `@total` annotation checks
4. Subset check
5. **Refinement verification (NEW)** — emit a verification-only
   Lean file (`def __thalesObligation_<n> ... := by thales_grind`;
   no runtime code) to a temp file, run `lake env lean`, scan for
   proof-term errors, surface as `TH0080` diagnostics.
6. Directive application
7. Totality verification (`@total`)
8. Emit

The runtime emitter (step 8) stays unchanged — runtime Lean has no
proof artifacts, so byte-match conformance is preserved exactly.

A new emitter module (`Thales/Emit/Verify.lean`) lowers the typed
AST to verification-only Lean. It shares predicate-lowering and
expression-lowering code with the runtime emitter but emits
obligation declarations with a tactic-block proof term at every
refinement slot.

**Hypothesis destructuring at each obligation site.** Each
refinement slot's obligation is emitted with the relevant
function/loop parameters bound, plus their `Float.IsSafeInteger`
hypotheses pre-destructured. The PoC validated this convention:

```lean
-- For an obligation depending on `n : Integer`:
def __thalesObligation_<n> (n : Float) (hn : Float.IsSafeInteger n)
    <other parameters and hypotheses> :
    <slot predicate applied to value expression> := by
  obtain ⟨n_int, rfl, hlow, hhigh⟩ := hn
  -- ...repeat for each refined parameter...
  thales_grind
```

This convention means the discharger sees `Int` witnesses in scope;
the custom tactic only needs to do the rewrite-and-`omega` step,
not the destructuring. Note that the emitter generated the
hypothesis structure, so it has the information needed to emit the
right `obtain` patterns; an auto-destructuring tactic is
unnecessary.

**Homomorphism axioms.** The verifier maintains a small set of
axioms that capture the IEEE 754 ↔ Int homomorphism within the
safe-integer range. The complete set, soundness sketches, and
audit conventions are in **Part III**. Each axiom is annotated in
source with `-- AXIOM(thales): ...` so that
`git grep "AXIOM(thales)"` enumerates the trust base.

**`omega` and `abbrev` interaction.** The discharger does not
unfold `abbrev`s used in hypotheses during preprocessing.
Implementation note discovered during the PoC: the verifier either
emits literal numeric bounds (`9007199254740991`) directly, or
emits an `unfold minSafe maxSafe at *` step before the discharger.

Refinement verification runs *before* directive application, so
refinement-violation diagnostics can be suppressed by
`@thales-expect-error TH0080` like any other TH code. TH9002
correctly blocks emission when a refinement violation has been
suppressed.

**`--no-emit` behavior:** the verification phase runs
unconditionally; `--no-emit` only skips the runtime emit step. So
`thales --no-emit file.ts` reports refinement violations.

**Future direction (post-0.9):** eventually embed Lean directly
into the `thales` binary so verification can run in-memory rather
than via subprocess to `lake env lean`. The 0.6 → 0.9 ladder
keeps the shell-out approach because it reuses the existing
`@total` plumbing and is well-understood.

**Hypothesis plumbing.** When the verification emitter encounters a
TS conditional (`if (cond) ... else ...`) or ternary
(`cond ? a : b`), it lowers to Lean's *binding* form of `if`:

```lean
if h : <cond_lowered> then <then_branch> else <else_branch>
```

The hypothesis `h` (or its negation in the else branch) is in scope
inside each branch; the discharger automatically sees all in-scope
hypotheses. For chained `&&` in the condition (`if (a && b) ...`),
the lowering fans out so each conjunct becomes its own named
hypothesis (`if h₁ : a then if h₂ : b then ... else ... else ...`).

In 0.8 (when verification ships), only `if`/`else`/ternary
narrowings reify hypotheses for the discharger. Switch-on-typeof
and other narrowing constructs go through standard widening (no
narrowed hypothesis added) — those can be extended in post-0.9
work without breaking the 0.6 → 0.9 corpus.

**Source mapping (Lean error → TS position).** Each refinement
obligation is emitted as a uniquely-named declaration:

```lean
def __thalesObligation_42 ... := by thales_grind
```

Thales maintains an in-memory side-table mapping each obligation
index to the TS source position. When `lake env lean` reports an
error mentioning `__thalesObligation_42`, Thales translates it to a
TS-positioned `TH0080` diagnostic via the side-table. For shape
details, see Part II, decision D20.

This is intentionally simpler than the TC39 TG4 source-map
standard. TG4's value (cross-tool consumption, IDE integration,
VLQ-encoded positional remapping) is real but not relevant for an
internal, ephemeral verification artifact that no other tool
consumes. A flat side-table is a strict subset of what TG4
supports, so a later upgrade — if/when an IDE or another tool
wants to consume Thales's obligation map — is a mechanical
translation, not a redesign.

**Verifier timeout.** `omega` can in principle hang on hard
problems, even though the predicate sublanguage's bounded-fragment
design makes this unlikely. 0.8 sets a per-`lake env lean`
invocation timeout (initial value 30s, configurable) using the
same process-supervision pattern as `@total`. Timeout surfaces as
`TH0080` with a note that the obligation timed out rather than
being refuted. For other failure modes, see Part II, decision D19.

### 8. MAX_SAFE_INTEGER baked into `Integer` (M1)

L3 reflection's per-value fidelity — that every `Integer`-typed
Float maps to a unique `Int` and `Float.ofInt` is exact at that
point — holds *only* within the JS safe-integer range
(±(2⁵³−1)). Outside that range, integer-valued Floats exist (e.g.,
`2^53` itself is exactly representable), but Float arithmetic on
them rounds in ways that desynchronize from `Int` arithmetic. So
the safe-integer bound is required to make the *reflection* sound
for any individual value.

(Note: bounding individual *operands* is necessary but *not
sufficient* to make arithmetic *operations* preserve refinement —
`MAX_SAFE + 1` is integer-valued but exceeds the bound, and
`MAX_SAFE + MAX_SAFE` rounds in Float arithmetic. That's why
decision 6 only places a small set of operations on the static
sound table, and the rest widen.)

Therefore the prelude `Integer` predicate bakes in safety:

```ts
/** @refine x => Number.isInteger(x) && x >= Number.MIN_SAFE_INTEGER && x <= Number.MAX_SAFE_INTEGER */
type Integer = number;
```

`Nat`, `Byte`, `Bit` inherit safety automatically (subtypes of
`Integer`). Programmers who want unbounded integer math use
`bigint` (already supported, lowers to Lean `Int` with no
refinement layer).

Consequences:

- The grammar's `INT_LIT` accepts negative literals
  (`x >= -9007199254740991`).
- A literal outside the safe range (e.g.,
  `let n: Integer = 9007199254740993`) is a refinement violation
  at type-check time. The "warning if integers exceed safe limits"
  from the original pitch is automatic and is an *error*, not a
  warning.
- No separate `SafeInteger` type. `Integer` *means* JS-safe.

**Note on negative zero.** `Number.isInteger(-0)` returns `true`,
so `-0` is a member of the JS-side `Integer` predicate. Lean
preserves `-0.0` as a distinct `Float` value with its own bit
pattern, which gives us room to model `-0` faithfully in the
verifier. Detailed handling — and a small soundness wrinkle in
the PoC's axiom set at `n = 0` — is deferred to Milestone D2 /
0.8 (see Part X open question 6). 0.6 and 0.7 carry no
verification phase, so neither version is affected.

### 9. Sublanguage extension: named-constant atoms

The sublanguage recognizes `Number.MIN_SAFE_INTEGER` and
`Number.MAX_SAFE_INTEGER` as constant atoms with values
`-9007199254740991` and `9007199254740991`. They are accepted in
both predicate position (in `@refine`) and in narrowing-guard
position (in `if`-condition pattern matching). The grammar update
is folded into decision 5.

### 10. Introducing refined values: prelude guards + inline patterns; no `as Integer`

Three sources of refined values:

1. **Literals in range** — handled trivially by static check.
2. **Arithmetic** — handled by the obligation pipeline (decision 6).
3. **Narrowing from a wider type** — handled by **both** of the
   following two pathways:

**(C1) Inline predicate narrowing.** Thales recognizes an `if`
condition whose body matches the refinement's effective predicate
exactly, and narrows the variable:

```ts
if (Number.isInteger(n) && n >= Number.MIN_SAFE_INTEGER && n <= Number.MAX_SAFE_INTEGER) {
  // n: Integer here
}
```

**(C2) Prelude-helper guards.** The prelude ships `declare`d guards
that Thales recognizes by name as narrowing guards. Each has a
matching JS runtime body whose return value is exactly the
refinement's predicate, so the guard's behavior at runtime is
consistent with what the type-checker assumes about it.

```ts
// Thales/TS/Prelude.d.ts
export declare function isInteger(n: number): boolean;
export declare function isNat(n: number): boolean;
export declare function isByte(n: number): boolean;
export declare function isBit(n: number): boolean;
```

Implementation: extend `Thales/TypeCheck/Narrowing.lean` with a
small "refinement-narrowing" guard kind, parallel to the existing
`typeofEquals`/`instanceOf`/etc. The 0.7 implementation matches
both prelude guards (by name) and inline patterns (by AST shape);
0.9 replaces the hardcoded matchers with a parser-driven
recognizer (see Part II, decision D22).

**No `as Integer` cast.** Unchecked refinement assertions defeat
the verification framework. Forward-compatible: can be added later
as a TH-warning code.

**No user-defined type guards (`x is T`).** That's a much bigger
feature that intersects every narrowing concern in TS, not just
refinement types. Defer.

### 11. Stdlib refinement specifications: minimal initial set (D2)

Four entries ship, each implemented as a hardcoded special-case in
the type-checker (Thales does not have general TS overload
resolution; defer that):

- **`Array<T>.length: Nat`** — builtin-type-table entry. Every
  array length is a Nat by JS spec. Type-checker change to the
  `length` property type for arrays.
- **`string.length: Nat`** — builtin-type-table entry, same logic.
- **`Math.abs(n: Integer): Nat`** — special-case in the
  type-checker: when the call expression's callee is `Math.abs`
  and the argument's type is `Integer` or a subtype thereof, the
  result type is `Nat`.
- **`Math.abs(n: Nat): Nat`** — preserves; same special-case logic
  recognizes `Nat` subtype.
- **`Math.abs(n: Byte): Byte`**, **`Math.abs(n: Bit): Bit`** —
  same principle: `Math.abs` preserves any non-negative
  refinement. The four overloads instantiate this principle;
  0.9's user-defined-refinement work generalizes it.
- For all other call shapes, `Math.abs(n: number): number` (TS lib
  default).

Note that `arr.length` returning `Nat` is a *typing* change, not a
user-facing `@refine` annotation. Programmers don't write this;
Thales knows it.

Deferred (explicitly *not* in the 0.6 → 0.9 ladder):

- `Math.floor`/`ceil`/`trunc`/`round` — return `number` because of
  NaN/Infinity for non-finite input. Typing them as `Integer`
  would be unsound. Defer until Thales has `Integer | NaN` or a
  finite-input precondition pattern.
- `Math.min`/`max`/`pow` — not load-bearing; six-line user code
  with refinement-aware obligations covers the use case. (See
  Part XI for the overload sketches a future version might
  ship.)
- `parseInt`, `Number(bigint)` — return `number`; user narrows.
- **Array bounds-checking** — `arr[i]` does *not* require
  `i < arr.length` across 0.6 → 0.9. That's a separate, much
  bigger refinement (in-range indices with dependent
  length-tracking) that belongs to a future "non-empty array /
  safe-index" milestone.

### 12. Diagnostic codes (and severity)

`TH0080`–`TH0089` reserved for refinement types. Initial allocation:

| Code     | Severity | Meaning (user-facing message)                                                |
| -------- | -------- | ---------------------------------------------------------------------------- |
| `TH0080` | error    | Refinement obligation not discharged                                         |
| `TH0081` | error    | Refinement predicate not recognized                                          |
| `TH0082` | error    | `@refine` alias must have base type `number` or another refined alias        |
| `TH0083` | error    | Literal value out of range for refinement type                               |
| `TH0084` | error    | Cast to refinement type not permitted                                        |
| `TH0085` | error    | Multiple `@refine` annotations on one type alias                             |
| `TH0086` | info     | Arithmetic on refinement type widens to `number`                             |
| `TH0087` | error    | Refinement predicate references variable not bound by the lambda parameter  |

`TH0088`–`TH0089` reserved for additions during the 0.6 → 0.9
implementation.

**Severity levels are introduced in 0.7 along with `TH0086`** (the
field itself is added as a stub in 0.6 to keep diagnostic
infrastructure changes small per version, but no `info` codes
ship until 0.7). Prior TH codes were uniformly errors; the
diagnostic infrastructure (`Thales/TypeCheck/Diagnostic.lean`)
gains a `Severity` field (`error | info`; `warn` reserved for
later). `error` blocks emission as before; `info` is reported but
does not block. `@thales-expect-error TH<code>` works for both
severities — a user who has explicitly considered an `info` site
can suppress it.

`TH0086` triggers conservatively: only when *both* operands of a
binary arithmetic op are refined-int and the operator/operand-types
pair is *not* on decision 6's static sound table. Forms that *are*
on the table do not fire `TH0086`.

User-facing messages do not name the discharger (`omega`/`grind`/etc.)
and do not mention version numbers. Implementation comments and
`docs/errors.md` may explain mechanism, but the diagnostic itself
describes the *phenomenon*, not the *means*.

`TH0080` is a single code covering all undischarged obligations
regardless of which refinement is involved — the diagnostic message
carries the type name. Matches `tsc`'s pattern of one code (e.g.
`TS2322`) covering many "not assignable" cases; keeps the directive
machinery simple.

### 13. Conformance contract

By L3 transparency, runtime byte-match holds automatically.
Refinement-typed accepting programs lower to identical runtime Lean
as their unrefined counterparts. The verification phase
(decision 7) is sidecar — it never modifies the runtime emit.

**No changes to `scripts/run-examples.js` are required.** The
harness's `diagKey` matching already accommodates Thales adding
`TH####` codes on top of `TS####`.

`Math.abs(Integer): Nat` returns the same runtime `Float` value as
`Math.abs(number): number` — refinement is type-level, not
runtime-level. So `Math.abs` does *not* get a special runtime
helper. This is documented in `docs/runtime.md`.

### 14. Scope lock — what is *deliberately not shipping*

See Part IX for the complete lock list, broken out per version.

### 15. Documentation updates

See Appendix A for per-version documentation file changes.

### 16. Implementation across the 0.6 → 0.9 version ladder

The implementation plan is in **Part VII** (revised 2026-05-06).
The original spec's six-milestone list (A–F, ~3–7 days each)
intended for a single 0.6 release has been refined into a
finer-grained graph and re-grouped across four versions, each
shipping independently as workable software.

---

## Part II — Decisions added during 2026-05-06 roadmap revision

External review (PAL `thinkdeep` second look) plus a codebase audit
surfaced gaps that the 16 locked decisions left unspecified. Each
decision below resolves one such gap. They live here, separate from
Part I, so the revision history is auditable.

### D17. Mixed-refinement arithmetic table extension (Milestone B / B.5)

The static sound table in decision 6 covers only homogeneous pairs
(`Byte + Byte`, `Bit + Bit`, etc.). Because the lattice allows
`Bit <: Nat`, `Byte <: Nat`, `Nat <: Integer`, mixed-refinement
expressions like `byte + bit` are expressible. Decision needed.

**Decision: extend the static table with a small explicit set of
mixed-pair entries; do not derive a general subtype-join.** The
extension:

| Operands              | Result    |
| --------------------- | --------- |
| `Byte + Bit`          | `Nat`     |
| `Bit + Byte`          | `Nat`     |
| `Nat + Bit`           | `Nat`     |
| `Bit + Nat`           | `Nat`     |
| `Nat + Byte`          | `Nat`     |
| `Byte + Nat`          | `Nat`     |
| `Integer + Byte`      | `Integer` |
| `Byte + Integer`      | `Integer` |
| `Integer + Bit`       | `Integer` |
| `Bit + Integer`       | `Integer` |
| `Integer + Nat`       | `Integer` |
| `Nat + Integer`       | `Integer` |

Subtraction follows the same lattice but never falls into `Nat` or
`Byte` because subtraction can produce a negative; mixed-pair
subtraction lands in `Integer`. Multiplication is similarly
generalized only where the magnitude argument still applies (e.g.,
`Byte * Bit ≤ 255 < MAX_SAFE`, lands in `Nat`).

Rationale: closing the table under arbitrary subtype joins would
need a join function and a general "promote to least common
supertype" pass — disproportionate complexity for a feature whose
useful cases all collapse to one of the rows above. Conversely,
widening straight to `number` at the first non-table site loses
too many positive-narrowing wins.

The extension is a half-day of code and lives in Milestone B.5 (a
new prerequisite, ordered between B and {C, D1}); locking it before
either D1 or D2 starts prevents both from chasing a moving table.

### D18. TH0086 + TH0080 interaction rule (Milestone B / D2)

Decision 6 introduced `TH0086` (info) and decision 12 introduced
`TH0080` (error). The original spec implied both could fire on the
same site (the corpus's `add(a: Integer, b: Integer): Integer`
expects both); without a rule, an info that always co-fires with an
error is noise.

**Decision: TH0086 means "no static-table entry; the verifier was
asked." It fires whenever a binary refined-int arithmetic site
falls off the static sound table _and an obligation is generated_.
TH0080 fires when that obligation fails. They co-occur by design
when an operation is unverifiable; the info is the breadcrumb that
explains what the error was about.**

Suppression rules:

- `@thales-expect-error TH0086` suppresses only the info; if the
  obligation still fails, TH0080 still fires.
- `@thales-expect-error TH0080` suppresses only the error; the
  info remains, signalling that verification was attempted.
- The two codes are independent suppression targets: a corpus
  example documenting "this fails verification" suppresses both.

This is consistent with how `tsc`-mirroring diagnostics already
work: every diagnostic is independently suppressible by code.

### D19. Subprocess error model (Milestone C / C.5)

Decision 7 covered the happy-path subprocess driver and the timeout
case. It didn't cover the broader failure surface (Lean process
killed by OOM, malformed temp file, lake binary missing, elaboration
errors with no obligation reference, etc.).

**Decision: keep TH0080 as the only verification diagnostic users
see; distinguish failure modes through the diagnostic _note_, not
through new TH codes.**

| Failure mode                                        | Surfaced as                                                |
| --------------------------------------------------- | ---------------------------------------------------------- |
| Timeout                                             | TH0080 with note `obligation timed out (N s)`              |
| Lean process killed (OOM / SIGKILL)                 | TH0080 with note `verifier killed (signal N)` + first 200 chars of stderr |
| `omega` failed for a recognized obligation index    | TH0080 with predicate/context from registry (standard)     |
| Lean exited non-zero, no obligation reference, recognizable elaboration text | TH0080 with note `internal: verifier rejected the generated Lean (first 200 chars: ...)` (emitter bug, not user-program bug) |
| Lean exited non-zero, no recognizable text          | TH0080 with note `internal: unexpected verification error` + first 200 chars of stderr |

Conditions that bypass TH0080 entirely (treat as harness errors,
exit non-zero, no per-obligation surfacing):

- `lake env lean` not found / wrong toolchain. The compiler exits
  with a clear "verifier toolchain missing" message; no per-file
  TS diagnostic.
- Temp-file write failure (disk full, permission denied) during
  obligation emission. Same: hard exit with a single
  "verification scratch dir unwritable" line.

Rationale: a single user-facing TH code with structured notes
matches how `tsc` surfaces errors and avoids a combinatorial
explosion. Internal errors are still individually identifiable by
their note prefix (`internal:`, `verifier killed`, `obligation
timed out`), so a log-grep for "TH0080 internal:" gives the
operations team a clean filter without a separate diagnostic
taxonomy.

The note-prefix conventions are pinned in
`Test/Emit/VerifyDriverTest.lean` so a renaming doesn't silently
break log dashboards.

### D20. Source-map registry shape (Milestone C)

The original spec's `ObligationInfo` carried `ts_file` plus
position fields, with a "per-file counter that resets per file"
comment. This implies multi-file batching.

**Decision: drop `ts_file` from `ObligationInfo`. The verifier
subprocess is invoked once per `thales` process (i.e., once per TS
file), and the registry only ever holds obligations from the file
currently being checked. The registry key is the per-invocation
`Nat` index, full stop.**

Each entry carries `value_span` and `slot_span` (per the tracer-4
finding in Part V) plus `predicateText` and `contextDesc` strings
for diagnostic notes. The binder/hypothesis structure used by the
emitter is computed at emission time and does not need to be in the
registry.

Future batching, if it ever ships, will reintroduce `ts_file` (or
prepend a file hash to the index). The 0.6 design pays no
complexity for that future today.

### D21. `@throws` non-returning narrowing (new milestone D0.5)

The boundary pattern in D1 (`fromUnknown`) is

```ts
function fromUnknown(raw: number): Integer {
  if (!Number.isInteger(raw)) throw new RangeError(...);
  return raw; // raw must carry the narrowed Integer here
}
```

The current narrowing pass at `Thales/TypeCheck/Check.lean:359-388`
narrows _inside_ each branch of an `if` and then unconditionally
reverts to the pre-branch bindings after the `if` ends. Whether
one branch terminated by throwing makes no difference — post-`if`,
every binding is back to its pre-branch type. So the `return raw`
above sees `raw : number`, not `raw : Integer`, and the boundary
pattern fails to type-check. Audit confirmed (Part VIII).

**Decision: add a focused "definitely non-returning" recognizer to
the narrowing pass as a new D0.5 prerequisite issue. Scope is
deliberately narrow: recognize exactly the syntactic shapes**

- a `then` (or `else`) block whose statement list ends in a
  bare `throw <expr>;`, or
- a `then`/`else` block whose statement list ends in a
  `return <expr>;`, or
- a `then`/`else` block whose statement list ends in a call to a
  `@throws`-annotated function with no `try` enclosing.

When such a block is detected, the post-`if` narrowing carries
forward whatever the _other_ branch's narrowing produced (or, when
the non-returning branch was the implicit `else`, the consequent's
narrowing).

**Out of scope:** general unreachability analysis, infinite-loop
detection, exhaustive flow analysis through nested `try`/`finally`,
analysis through user-defined helpers (beyond honoring `@throws`).
This is approximately 30 lines of code in `Narrowing.lean` plus a
handful of tests under
`Test/TypeCheck/NonReturningNarrowingTest.lean`.

Rationale for the milestone split: keeping this in D1 would push
D1 above the four-day budget and mix a control-flow concern with
the refinement-narrowing concern. As its own issue, it reviews and
ships in half a day, and D1 then cleanly depends on it.

### D22. Predicate recognizer hand-off (Milestone D1 → E)

D1 ships an inline predicate matcher for narrowing. That matcher
is hardcoded against the four prelude predicates' AST shapes —
duplicating, by design, the hardcoded recognizer that Milestone A
ships for `@refine` aliases. Milestone E then introduces the real
predicate parser.

**Decision: when E lands, both the A recognizer and the D1 matcher
are replaced by the parser-produced AST. The two recognizers
should not survive in any form post-E.** A regression test added
in E ("user-written `@refine` whose AST normalizes to a prelude
predicate narrows just like the prelude predicate") pins this
behavior so that future refactors don't accidentally regrow the
hardcoded recognizer.

### D23. Tour validation strategy (Milestone 0 / F)

Milestone 0 ships annotated `.ts` files that say
`// ✓ thales accepts` or `// ✗ thales: TH0083 (...)`. These
annotations could drift from reality across A–E without anyone
noticing, and a manual "doc-vs-impl diff" is fragile.

**Decision: add a small standalone `scripts/validate-tour.js` (or
a similar Lean test) in Milestone F that parses the `// ✓` and
`// ✗ TH00xx` comments out of each tour file and confirms the
actual compiler behavior matches.** The validator is *not* part of
the conformance harness — tour files are still documentation, not
fixtures, and the validator's failure mode is "the tour is lying,"
not "the compiler is wrong." It runs in CI alongside the harness.

If the validator turns out to be more than a day's work, fall back
to marking the tour "illustrative, not normative" and accept
drift, documented in `docs/refinement-types-tour/README.md`.

---

## Part III — Soundness & trust base

This part is the audit-ready story for the verification phase. It
exists so that a reviewer who has not read Parts I–II or the PoC
can confirm, in one sitting, what the verifier assumes about the
relationship between `Float` (the runtime carrier) and `Int` (the
reasoning surface used by `omega`).

The companion implementation lives in `Thales/Emit/Verify.lean`
(when 0.8 lands; the PoC sits on `feat/thales-grind-poc`). When
0.8 ships, this section is promoted to a top-level
`docs/refinement-soundness.md` file (see Appendix A). When the
trust base changes, this section / file is the canonical place
to update.

### Scope

Refinement values are carried at runtime as IEEE 754 doubles
(`Float`), exactly like every other `number` in Thales-TS. The
verifier never reasons about general `Float` arithmetic. Every
refinement obligation is reflected to a statement about `Int`,
which is what `omega` discharges.

The reflection rests on the predicate

```lean
def Float.IsSafeInteger (x : Float) : Prop :=
  ∃ n : Int, x = Float.ofInt n ∧ minSafe ≤ n ∧ n ≤ maxSafe

abbrev minSafe : Int := -9007199254740991  -- -(2^53 - 1)
abbrev maxSafe : Int :=  9007199254740991  --  (2^53 - 1)
```

`Integer`, `Nat`, `Byte`, `Bit` all lower to this predicate plus a
range tightening (`0 ≤ n` for `Nat`, `0 ≤ n ∧ n ≤ 255` for `Byte`,
`0 ≤ n ∧ n ≤ 1` for `Bit`). The destructuring tactic
`obtain ⟨n_int, rfl, hlow, hhigh⟩ := hn` turns a hypothesis
`Float.IsSafeInteger x` into an `Int` named `n_int` together with
the two bound hypotheses. Once every refined operand is
destructured this way, the goal is an `Int` statement and `omega`
takes over.

### Foundational fact

Everything below rests on a single property of IEEE 754 binary64:
every integer in the closed interval `[-(2^53 - 1), 2^53 - 1]` is
exactly representable as a double, with no rounding. Binary64 has
a 53-bit mantissa with an implicit leading bit, giving exact
representation for `|n| ≤ 2^53`; we exclude `±2^53` from
`IsSafeInteger` to align with JavaScript's
`Number.MAX_SAFE_INTEGER`, where adjacent integers above `2^53`
collide under round-to-nearest. Inside the safe range,
`Float.ofInt` is therefore injective and strictly order-preserving,
and the standard binary IEEE 754 arithmetic operations (`+`, `-`,
unary `-`) are exact when both operands and the mathematical
result stay in range.

This property is not a theorem we have proved; it is a fact about
the IEEE 754 standard. The axioms below are corollaries of it.
They are intentionally narrow: each one states a single
homomorphism-like equation specialized to safe integers, rather
than a general claim about `Float`.

### The 0.8 axiom set

These axioms are introduced when 0.8 ships, in `Thales/Emit/Verify.lean`
and consumed by the `thales_grind` macro. Every axiom is annotated
in source with `-- AXIOM(thales): ...` so that
`git grep "AXIOM(thales)"` enumerates the trust base.

#### Equality / structural

```lean
axiom Float.ofInt_neg (n : Int) :
    -(Float.ofInt n) = Float.ofInt (-n)
```

Negation on the safe range is exact: IEEE 754 binary64 has a
symmetric mantissa, so `-(double n)` flips the sign bit and
recovers `double (-n)` bit-for-bit. The rewrite direction (inner
negation through) is chosen so that `simp only [Float.ofInt_neg]`
normalizes toward "all `Float.ofInt` calls have an `Int`
literal/term inside," which is the form `Float.ofInt_lt`/`_le`
expect. Trust weight: low (direct corollary of representability).

```lean
axiom Float.ofInt_add (a b : Int) :
    Float.ofInt a + Float.ofInt b = Float.ofInt (a + b)

axiom Float.ofInt_sub (a b : Int) :
    Float.ofInt a - Float.ofInt b = Float.ofInt (a - b)
```

Addition and subtraction are exact when both operands and the
result lie in the safe range. The verifier emits these axioms as
unconditional rewrites; soundness is preserved because every
obligation in which they fire arrives with hypotheses that bound
both operands inside the safe range, and `omega` will discharge
the result-bound obligation separately. If the result-bound check
fails, the rewrite is irrelevant — `omega` already refused. Trust
weight: medium (correct only under the bound invariant the
surrounding obligation establishes).

`Float.ofInt_sub` is needed by the unary-`-` rule on `Nat` (which
lowers to `0 - n`) and by the `half`-style obligations in the D2
corpus.

#### Order

```lean
axiom Float.ofInt_lt (a b : Int) :
    Float.ofInt a < Float.ofInt b ↔ a < b

axiom Float.ofInt_le (a b : Int) :
    Float.ofInt a ≤ Float.ofInt b ↔ a ≤ b
```

Order is preserved exactly on the safe range because no rounding
occurs. These axioms are stated for arbitrary `Int` arguments;
that is sound because outside the safe range, monotonicity of
`Float.ofInt` still holds for the IEEE 754 round-to-nearest mode
(rounding cannot flip a strict order between distinct integers
separated by at least one). Trust weight: low.

#### What's *not* in the trust base

No axiom is shipped for multiplication, division, modulo, or any
bitwise operation. The static sound table in decision 6 handles
every multiplication and bitwise case the corpus across the
0.6 → 0.9 ladder actually emits (`Bit & Bit`, `Byte * Byte`,
etc.), and these reduce to small-integer arithmetic that `omega`
discharges directly without a homomorphism step.

If a future corpus example needs a multiplication-on-safe-integers
axiom, it must be added here, with its own soundness sketch, and
marked `-- AXIOM(thales): ...` so the trust-base audit picks it up.

### Risks (where a sound-looking axiom could be silently wrong)

These risks are documented so that a future change to Lean, the
emitter, or the corpus does not accidentally invalidate the trust
base.

- **Lean's `Float.ofInt` is not currently a verified primitive.**
  It is part of the Lean prelude and its observable behavior
  matches the IEEE 754 conversion on the safe range. A future
  change to its rounding mode (e.g., truncate-vs-round-to-nearest
  above the safe range) does not affect the axioms — they are
  stated only for inputs that the surrounding obligation
  hypothesis confines to the safe range — but a change to the
  safe-range case would. The `Test/Emit/SoundnessTest.lean`
  fixture (added in Milestone D2 / 0.8) pins `Float.ofInt`
  behavior at boundary values to catch a silent toolchain change.
- **Signed zero and the `Float.ofInt_neg` axiom.** `Float.ofInt 0`
  is `+0.0` (bit pattern `0`), but `-(Float.ofInt 0)` is `-0.0`
  (bit pattern `2^63`). Under Lean's bit-level propositional
  equality on `Float`, the universally-quantified
  `Float.ofInt_neg` axiom is therefore false at `n = 0`. The PoC
  doesn't trip the bug because every use of the axiom occurs
  with a hypothesis like `n_int < 0` in scope, but the
  axiom-as-stated is a latent unsoundness. Resolution is
  deferred to Milestone D2 / 0.8; the leading direction is
  either a domain restriction on the axiom (`n ≠ 0`) or a small
  type-system rename (e.g., introducing a `TSInteger` type that
  captures the JS-side notion including `-0`) that lets the
  axioms be stated cleanly. See Part X open question 6.
- **NaN and infinity.** Both are unreachable from refined
  integers: `IsSafeInteger` excludes them by construction
  (`Float.ofInt n` is finite for every `Int`). The axioms
  therefore never need to consider them.
- **`omega` reasons in classical real arithmetic.** Any
  counter-model for an `Int` goal `omega` accepts must also be a
  counter-model in IEEE 754 doubles for the corresponding `Float`
  goal — the axioms are the bridge that makes this reduction
  valid. If an axiom is ever wrong, `omega` will faithfully
  accept goals that are false on the runtime carrier, which is
  the worst kind of failure. Hence the small, auditable surface.

### Audit checklist

When the verifier or its trust base changes, walk this checklist
before merging:

1. `git grep "AXIOM(thales)"` enumerates exactly the axioms
   listed above. Each new entry has its own subsection with
   signature, soundness sketch, and trust weight.
2. The `thales_grind` macro's `simp only [...]` list matches the
   axiom set. An axiom that ships without being added to the
   macro is dead weight; an axiom in the macro that isn't listed
   here is a trust-base leak.
3. `Test/Emit/ObligationEmissionTest.lean` covers each axiom in
   at least one golden output. If an axiom is removed, its
   golden tests are removed in the same change.
4. `Float.IsSafeInteger`, `minSafe`, `maxSafe` are unchanged —
   these pin the meaning of "safe range" that every axiom
   assumes. A change here invalidates every soundness sketch.

### Future generalization

User-defined `@refine` types ship in 0.9. At that point the trust
base may need rules for the additional predicates users can
write. The intent is to keep the same shape: each new constructor
of the predicate sublanguage gets one or two axioms relating its
`Float` form to its `Int` form, each with its own soundness
sketch. If that shape stops scaling — e.g., a user wants
`Math.sqrt`-bounded refinements (post-0.9 work) — the design
should reach for a Mathlib-backed `Float`/`Real` library rather
than growing the hand-axiomatized trust base.

---

## Part IV — Corpus examples

Each accepts under refinement-typed Thales unless marked
expected-failure; `tsc` accepts them as ordinary `number` programs
in all cases. The `[ships in: X]` tag on each example identifies
the earliest version where the example becomes a corpus fixture.

1. **`function negate(n: Integer): Integer { return -n; }`**
   `[ships in: 0.7]` — unary negation on `Integer`. Sound by static
   table (`|MIN_SAFE| = MAX_SAFE`). The simplest closed operation;
   no obligation. Requires the static-table machinery from 0.7;
   in 0.6 the function would fail because `-n` widens.

2. **`function double(b: Byte): Nat { return b + b; }`**
   `[ships in: 0.7]` — `Byte + Byte = Nat` by static table. Result
   range `[0, 510]`, well within `Nat`. No obligation.

3. **`function bitAnd(a: Bit, b: Bit): Bit { return a & b; }`**
   `[ships in: 0.7]` — bitwise on `Bit`, sound by static table.

4. **`function clamp(b: Byte): Byte { return b > 200 ? 200 : b; }`**
   `[ships in: 0.7]` — both ternary branches return `Byte` values
   (`200` is a `Byte` literal; `b: Byte` already). The 0.7 example
   does *not* exercise verification — it works at the type level.
   In 0.8 the verification emitter additionally reifies the
   conditional with the `b > 200` hypothesis available at each
   slot, but for `clamp` the obligations discharge trivially.

5. **`function abs(n: Integer): Nat { return Math.abs(n); }`**
   `[ships in: 0.6]` — stdlib refinement-aware overload (decision
   11). Lands in 0.6 because no arithmetic, narrowing, or
   verification is required: the `Math.abs` overload is a
   type-checker special case that produces `Nat` directly.

6. **`function fromUnknown(raw: number): Integer`**
   `[ships in: 0.7]` — *the boundary pattern.* Demonstrates how
   an externally-supplied `number` is narrowed via the prelude
   guard:

   ```ts
   /** @throws RangeError */
   function fromUnknown(raw: number): Integer {
     if (isInteger(raw)) return raw;
     throw new RangeError("not a safe integer");
   }
   ```

   The narrowed `raw: Integer` in the then-branch comes from the
   `isInteger`-recognized prelude guard (decision 10's C2). The
   throw-branch satisfies the function's `@throws` obligation and
   does not need to return `Integer`. The post-narrowing flow
   relies on Part II decision D21.

7. **Out-of-range literal — expected failure.**
   `[ships in: 0.6]`

   ```ts
   // @thales-expect-error TH0083
   const TOO_BIG: Integer = 9007199254740993;
   ```

   The literal exceeds `MAX_SAFE_INTEGER`; the static
   literal-in-range check fails immediately. Lands in 0.6 because
   it requires only the lattice + literal-range check.

8. **Arithmetic non-closure — expected failure.**
   `[ships in: 0.8 with TH0080; 0.7 ships a 0.7-flavored variant]`

   ```ts
   // @thales-expect-error TH0080
   // @thales-expect-error TH0086
   function add(a: Integer, b: Integer): Integer { return a + b; }
   ```

   Demonstrates the central design constraint:
   `Integer + Integer` widens to `number`. In 0.8 the obligation
   `MIN_SAFE ≤ a + b ≤ MAX_SAFE` is generated and refused by
   `omega` (counterexample: `a = b = MAX_SAFE`). Per Part II
   decision D18, both diagnostics fire and both are suppressed by
   the directive pair. In 0.7 (no verification), the same source
   fails with `TH0086` *and* a regular type-mismatch
   (`number` not assignable to `Integer`), since no obligation
   pipeline exists to discharge widening — the corpus example
   ships in 0.7 with that exact diagnostic shape, then mutates to
   the TH0080 form when 0.8 lands.

9. **Division widens — expected failure.**
   `[ships in: 0.8 with TH0080]`

   ```ts
   // @thales-expect-error TH0080
   // @thales-expect-error TH0086
   function half(n: Integer): Integer { return n / 2; }
   ```

   `Integer / Integer` widens (`5 / 2 = 2.5`). In 0.8 the
   obligation `Number.isInteger(n / 2)` fails for odd `n`. Same
   shape as example 8.

10. **User-shadowed prelude type — accepted.**
    `[ships in: 0.6]`

    ```ts
    // No prelude import: user-defined Integer (different
    // semantics) coexists with the prelude name unused.
    type Integer = bigint;       // domain wants arbitrary precision
    function safeAdd(a: Integer, b: Integer): Integer {
      return a + b;              // bigint + bigint, no Thales refinement
    }
    ```

    Tests that not importing the prelude leaves names free for
    user definitions. Lands in 0.6 because no refinement
    machinery is invoked — the user's `Integer` carries no
    `@refine` annotation, so Thales treats it as an ordinary
    type alias.

11. **Import-rename pattern — accepted.**
    `[ships in: 0.6]`

    ```ts
    import { Integer as PreludeInteger } from "@thales/prelude";

    type Integer = string;       // user's own; no conflict
    const a: Integer = "hello";
    const b: PreludeInteger = 42;
    ```

    Tests that `import as` rename allows both the prelude type
    and a user-defined type with the same surface name to
    coexist. Lands in 0.6.

12. **Inner-scope shadowing — accepted.**
    `[ships in: 0.6]`

    ```ts
    import { Integer } from "@thales/prelude";

    const outer: Integer = 42;   // prelude's Integer

    function localOverride(): string {
      type Integer = string;     // shadows the import in this scope
      const inner: Integer = "hello";
      return inner;
    }
    ```

    Tests that function-local type aliases shadow imports per
    TS scoping. Lands in 0.6.

13. **Same-scope redeclaration — `tsc`-rejected.**
    `[ships in: 0.6]`

    ```ts
    import { Integer } from "@thales/prelude";
    // @ts-expect-error TS2440
    type Integer = string;       // duplicate identifier
    ```

    Tests that Thales does not need to add a separate diagnostic
    for redeclaration — `tsc` rejects this with TS2440 first,
    and the conformance contract carries the rejection through
    Thales unchanged.

---

## Part V — Source-map tracers (data-flow walkthroughs)

These four examples walk through the verification-pipeline data
flow end-to-end (TS source → typed AST → verification Lean →
registry entry → `lake env lean` → diagnostic). They are a
*thinking tool* for the design, not corpus examples; they're
chosen to stress different aspects of the source-map and
obligation-generation design and to expose friction points before
Milestone C commits.

Each tracer documents:
- **Source** — TS file the user would write.
- **What happens** — the type-checker / emitter walkthrough.
- **Verification Lean** — the `def __thalesObligation_<n>` shape
  we'd emit.
- **Registry entry** — the `ObligationInfo` written to the
  in-memory registry.
- **Outcome** — what the user sees.
- **Friction the tracer reveals** — design gaps surfaced by
  walking through this case.

### Tracer 1 — "Hello, obligation"

**Source.**

```ts
function takeInteger(x: number): Integer {
  return x;
}
```

**What happens.** The return statement assigns `x: number` into a
slot of type `Integer`. No static rule applies (the source isn't
a literal; not on the static fast-path table). Verifier generates
an obligation.

**Verification Lean (proposed).**

```lean
def __thalesObligation_0 (x : Float) :
    Float.IsSafeInteger x := by
  thales_grind
```

**Registry entry.**

```
0 → { ts_line: 2, ts_col: 10,
      predicateText: "Number.isInteger(x) && x in [MIN_SAFE_INTEGER, MAX_SAFE_INTEGER]",
      contextDesc: "return slot of `takeInteger` (type Integer)" }
```

**Outcome.** `omega` cannot prove the predicate for an arbitrary
`x : Float` (no info available). Lean error mentions
`__thalesObligation_0`. `TH0080` surfaces at `tracer-1.ts:2:10`.

**Friction revealed.** The obligation has to take the function's
parameters as Lean binders; it isn't a closed proposition. The
verification emitter must compute *the relevant scope at each
slot*: which parameters/locals the predicate references, and
which of those have refinement hypotheses available.

### Tracer 2 — "Narrowing rescue"

**Source.**

```ts
/** @throws RangeError */
function takeInteger(x: number): Integer {
  if (isInteger(x)) {
    return x;
  }
  throw new RangeError("not a safe integer");
}
```

**What happens.** Type-checker recognizes `isInteger` as a
narrowing guard (decision 10's C2). Inside the `then`-branch, `x`
has type `Integer` (not `number`). The return-slot type matches
the value type *syntactically*; no obligation is generated. The
throw branch satisfies `@throws`; the function as a whole is
well-typed.

**Verification Lean.** Empty for this function — no slot
mismatches, no obligations.

**Registry entry.** None. Counter doesn't increment.

**Outcome.** No `TH0080`. The verification Lean file may be
entirely empty for this source file (if it's the only function);
subprocess to `lake env lean` can be skipped.

**Friction revealed.** Many functions will produce zero
obligations (those whose refinements are fully discharged at the
type-checker level via narrowing or static rules). The pipeline
should detect an empty registry and *skip* the `lake env lean`
invocation entirely; otherwise we pay subprocess overhead for
trivial cases.

### Tracer 3 — "Conditional with hypothesis" *(highest-stress tracer)*

**Source.**

```ts
function offsetSign(n: Integer): Nat {
  return n < 0 ? -n : n;
}
```

**What happens.**

- *Then-branch* (`n < 0` true): the static sound table says unary
  `-` of `Integer` is `Integer`, so `-n : Integer`. But the slot
  is `Nat`. So an Integer-into-Nat obligation is generated, with
  `n < 0` available as a hypothesis from the ternary lowering.
- *Else-branch* (`n < 0` false): `n : Integer` flows into a `Nat`
  slot, with `¬(n < 0)` (i.e., `n ≥ 0`) as a hypothesis.

Both obligations need the discharger to use the conditional
hypothesis to prove non-negativity.

**Verification Lean (validated by PoC, see Part VI).**

```lean
-- two obligations, one per ternary branch.
-- The emitter destructures the IsSafeInteger hypothesis inline so
-- the Int witness `n_int` is in scope when thales_grind runs.
theorem __thalesObligation_0 (n : Float)
    (hn : Float.IsSafeInteger n) (hcond : n < Float.ofInt 0) :
    Float.IsSafeInteger (-n) ∧ -n ≥ Float.ofInt 0 := by
  obtain ⟨n_int, rfl, hn_low, hn_high⟩ := hn
  refine ⟨⟨-n_int, Float.ofInt_neg n_int, ?_, ?_⟩, ?_⟩ <;> thales_grind

theorem __thalesObligation_1 (n : Float)
    (hn : Float.IsSafeInteger n) (hcond : ¬ (n < Float.ofInt 0)) :
    Float.IsSafeInteger n ∧ n ≥ Float.ofInt 0 := by
  obtain ⟨n_int, rfl, hn_low, hn_high⟩ := hn
  refine ⟨⟨n_int, rfl, hn_low, hn_high⟩, ?_⟩
  thales_grind
```

**Registry entries.** Indices 0 and 1, distinct sub-expressions of
the ternary.

**Outcome.** Both `thales_grind` invocations succeed; no `TH0080`.

**Friction *originally* anticipated, *resolved* by the PoC.**
`omega`/`grind` on `Float` directly is intractable (IEEE 754 lacks
the algebraic structure needed). The PoC validated the resolution:
the emitter destructures `Float.IsSafeInteger` hypotheses into
`Int` witnesses before the discharger runs, and `thales_grind` is
a thin rewrite-and-`omega` macro on the Int side.

The L3 design (decision 2) anticipated the reflection but didn't
specify *how* it happens. Tracer 3 makes it concrete:

1. The emitter inspects the goal and hypotheses, identifies
   `Float` values with attached `IsSafeInteger` hypotheses.
2. The emitter introduces existential reflection witnesses inline
   via `obtain ⟨n_int, rfl, hlow, hhigh⟩ := hn`.
3. `thales_grind` rewrites by the homomorphism axioms and calls
   `omega` on the resulting `Int`-goal.

### Tracer 4 — "Non-closure failure"

**Source.**

```ts
function add(a: Integer, b: Integer): Integer {
  return a + b;
}
```

**What happens.**

- `a + b` — both operands `Integer`, operator `+`, not on the
  static sound table → result widens to `number`. **TH0086 fires
  (info)** at the operator site (decision 6 + D18).
- The `number`-typed result flows into the `Integer` return slot.
  Obligation generated.

**Verification Lean (proposed).**

```lean
def __thalesObligation_0 (a b : Float)
    (ha : Float.IsSafeInteger a)
    (hb : Float.IsSafeInteger b) :
    Float.IsSafeInteger (a + b) := by
  obtain ⟨a_int, rfl, ha_low, ha_high⟩ := ha
  obtain ⟨b_int, rfl, hb_low, hb_high⟩ := hb
  refine ⟨a_int + b_int, Float.ofInt_add a_int b_int, ?_, ?_⟩
  <;> thales_grind
```

**Registry entry.** Index 0; carries both `value_span` (the `a + b`
expression) and `slot_span` (the `Integer` return slot) per D20.

**Outcome.** `thales_grind` reflects to `Int`: `a_int, b_int : Int`
with `|a_int|, |b_int| ≤ MAX_SAFE_INTEGER`, goal
`|a_int + b_int| ≤ MAX_SAFE_INTEGER`. **False** (counterexample:
`a_int = b_int = MAX_SAFE_INTEGER`). `omega` correctly fails.

User sees two diagnostics:

```
info[TH0086]: arithmetic on `Integer` widens to `number`
 --> tracer-4.ts:2:10
  |
2 |   return a + b;
  |          ^^^^^

error[TH0080]: refinement obligation not discharged
 --> tracer-4.ts:2:10
  |
2 |   return a + b;
  |          ^^^^^
  = note: result flows into return slot of `add` (type `Integer`)
  = note: could not show that `a + b` satisfies `Number.isInteger(x) && x in [MIN_SAFE_INTEGER, MAX_SAFE_INTEGER]`
```

**Friction revealed.** Choosing the *right TS position* matters
for diagnostic UX. Three plausible spans:

- the return statement (`return a + b;` — the slot)
- the value expression (`a + b` — what fails the predicate)
- the function signature (`Integer` — the declared type)

Best UX: point the diagnostic at the **value** with a note about
the **slot**. So `ObligationInfo` carries both `value_span` and
`slot_span` (codified in D20).

### Design refinements surfaced by these tracers

1. **`ObligationInfo` carries scope, not just position.** Each
   obligation `def` is parameterized by relevant variables and
   their refinement hypotheses. The verification emitter performs
   scope analysis at each slot.
2. **Empty registry → skip subprocess.** When a source file
   produces no obligations, don't invoke `lake env lean`.
3. **`ObligationInfo` carries both `value_span` and `slot_span`.**
   Diagnostic underlines the value, references the slot in a note.
4. **`thales_grind` is the central undefined piece** in the
   original spec. The PoC concretized it (Part VI).

These four tracers may be repurposed as `Test/Examples/fixtures/`
self-tests during Milestone C, where their job *is* to stress the
architecture.

---

## Part VI — PoC outcomes (2026-04-30, branch `feat/thales-grind-poc`)

The proof-of-concept work on branch `feat/thales-grind-poc`
validated the L3 reflection design and the `thales_grind` mechanic
before Milestone C. The PoC artifact is `Test/PoC/RefinementGrind.lean`
with `Test/PoC/FINDINGS.md` summarizing outcomes.

### Phase A — Int-side obligations

| Tracer                       | Expected                          | Result   |
| ---------------------------- | --------------------------------- | -------- |
| 3a (negation of negative)    | succeed via `omega`               | GREEN    |
| 3b (non-negative pass-through)| succeed via `omega`              | GREEN    |
| 1 (no bounds info)           | fail under `fail_if_success`      | GREEN    |
| 4 (sum can overflow)         | fail under `fail_if_success`      | GREEN    |

**Notes.** One minor surprise: `omega` does not unfold `abbrev`s
when they're used as hypothesis bounds. We had to add
`unfold minSafe maxSafe at *` before `omega` to make the bounds
visible. This is a property of `omega`'s preprocessing, not a
soundness issue. For the Milestone C verification emitter, this
means: emit obligations with literal bounds (`9007199254740991`)
inlined, OR include an `unfold` step before the discharger.

### Phase B — Float-side reflection

**`Float.ofInt`:** present in stdlib (`Float.ofInt : Int → Float`);
no local definition needed.

**Reflection lemma `Float.IsSafeInteger`:** defined as a
definitional existential (Part III). No additional axiom required
to *state* the predicate.

**Homomorphism axioms used in PoC:**
- `Float.ofInt_neg : ∀ (n : Int), -(Float.ofInt n) = Float.ofInt (-n)`
- `Float.ofInt_lt : ∀ (a b : Int), Float.ofInt a < Float.ofInt b ↔ a < b`
- `Float.ofInt_le : ∀ (a b : Int), Float.ofInt a ≤ Float.ofInt b ↔ a ≤ b`

We needed `Float.ofInt_le` in addition to the two axioms originally
planned because `≥` unfolds to `≤` with swapped arguments, and the
macro needed to rewrite both forms. For 0.6, more homomorphism
axioms (`Float.ofInt_add`, `Float.ofInt_sub`) are added in
Milestone D2 for tracers that exercise arithmetic preservation;
they are listed in Part III.

**`thales_grind` macro:** v0.5 (rewrite + omega), no
auto-destructuring.

```lean
macro "thales_grind" : tactic => `(tactic| (
  simp only [Float.ofInt_neg, Float.ofInt_lt, Float.ofInt_le, ge_iff_le] at *
  unfold minSafe maxSafe at *
  omega))
```

The plan's v1 (auto-destructuring of `IsSafeInteger`) was not
attempted; the v0.5 form is sufficient because the emitter knows
which hypotheses to destructure (it generated them) and emits the
`obtain` directly. A tactic that auto-destructures every
`IsSafeInteger` hypothesis is unnecessary.

| Tracer (Float-side) | Manual proof | `thales_grind` |
| ------------------- | ------------ | -------------- |
| 3a                  | succeed      | succeed        |
| 3b                  | succeed      | succeed        |
| 1                   | (n/a — expected fail) | `fail_if_success` confirmed |
| 4                   | (n/a — expected fail) | `fail_if_success` confirmed |

### Soundness of the test mechanism

Originally each expected-fail example used `fail_if_success` plus
a trailing `sorry` to satisfy `example`'s requirement of a complete
proof term. We refactored to a `sorry`-free form:

```lean
example : True := by
  fail_if_success
    (have : <unprovable_proposition> := by try_to_prove)
  trivial
```

The PoC builds with **zero warnings**. The test logic is preserved:
if the prover ever succeeded on the unprovable proposition (a
soundness bug), `fail_if_success` would fail the build.

### Timing

| Measurement                        | Value     |
| ---------------------------------- | --------- |
| Warm compile of the PoC file       | ~0.43 s   |
| Number of theorem/example decls    | 10        |
| Per-obligation amortized cost      | ~43 ms    |

For Milestone C: a typical Thales source file might generate 10–50
refinement obligations. At ~43 ms per obligation, that's ~0.4–2.2
seconds for the verification phase per file — comfortably within
acceptable range.

### Verdict for Milestone C

**Green light.** The L3 reflection design is sound, the
`thales_grind` mechanics are tractable using a small handful of
axioms, and per-obligation cost is well under our budget.

### Risks not validated by the PoC

- **Arithmetic preservation axioms.** PoC axiomatized only `_neg`,
  `_lt`, `_le`. Adding `_add`, `_sub` (and any others needed for
  arithmetic-discharge obligations) is straightforward but expands
  the trust base. Each axiom is marked `-- AXIOM(thales): ...` so
  future work can swap them for proofs from Mathlib (Part III's
  `git grep` audit convention).
- **Per-file source-map registry behavior.** The PoC didn't
  exercise the registry. Wiring up the side-table and the
  Lean-error parser is a Milestone C task. Risk: low (the
  side-table is straightforward).
- **Larger predicate sublanguage stress.** The PoC's predicate set
  is `Number.isInteger` + bounded comparisons. The full
  sublanguage allows conjunctions, narrowing-derived bounds, and
  multiple variables in scope. The mechanism scales (`omega`
  handles all of these), but bigger proofs may stress timing.
  Milestone D1 includes a perf sweep at 1, 2, 4, 8, 16 stacked
  refinement-bound hypotheses to surface this if it bites.

---

## Part VII — Version ladder & milestone breakdown

This part is the implementation plan, expressed as four shippable
versions. The work is an *epic*, not a single feature; building it
as horizontal layers (parser fully → type-checker fully → emitter
fully → verifier fully) means the system isn't end-to-end working
until the very last step. The slicing below is *vertical*: each
version crosses every layer needed for that version's user value,
leaves the build green, and ships something a user could
meaningfully exercise.

The original spec (Part I, decision 16) listed six milestones
(A–F) intended for a single 0.6 release. After roadmap review
2026-05-06, the flat list was refined into a finer-grained graph
(B.5, C.5, D0.5 inserted; A and D1 split) and then re-grouped
across four versions. Splitting across versions front-loads
visible value (0.6 ships immediately useful documentation
primitives) and back-loads architectural risk (the verification
pipeline lands in 0.8 once the user-visible API has already been
deployed).

### Cross-version dependency graph

Milestones are named once and grouped under their target version.
Dependencies cross version boundaries — that's the point of the
ladder.

```
0.6 │  M0 ─→ A1 ─→ A2 ─→ F.6
    │
0.7 │  B ─→ B.5 ─→ ┬─ D0.5 ─→ D1a ─→ D1b ─→ F.7
    │              │
0.8 │              ├─ C1 ─┐
    │              ├─ C2 ─┴─→ C3 ─→ C.5 ─→ D2 ─→ F.8
    │
0.9 │  E ─→ F.9
```

Each `F.X` is a tiny per-version polish pass (CHANGELOG entry,
final consistency sweep on the docs that version touches, tour
validator update). Within 0.8, C and D2 are independently rooted
in C.5, so the obligation-emitter work and the verification-driver
work can run in parallel within that version.

### Per-version overview

Each version's section below has four parts: **what the user can
do**, **milestones it ships**, **what's still missing**, and a
**working TS example** (or two) that demonstrates the visible
value. The examples are normative — if a published version
doesn't make them work, the version slipped its scope.

---

### 0.6 — Refinement types as documentation primitives

**What the user can do.** Declare `Integer`, `Nat`, `Byte`, `Bit`
in function signatures, parameter lists, return types, and
variable declarations. Out-of-range literals fail at compile time.
`Math.abs` overloads return refined types. `Array<T>.length` and
`string.length` carry `Nat` instead of `number`. Code-as-
documentation: future readers see what a function expects and
returns at the refinement level, even though `tsc` and the
runtime see only `number`.

**Milestones.** M0 (tour) → A1 (lattice & literal range) → A2
(prelude surface & overloads) → F.6 (polish, CHANGELOG, tour
validator).

**What's still missing in 0.6.** No arithmetic on refined types
(any binary `+`, `-`, `*`, etc. produces `number`, which then
fails to assign back into a refined slot with a regular
type-mismatch error). No narrowing (`if (isInteger(x)) ...` is
not understood). No verification phase (so even when arithmetic
*could* be proven safe, the tooling doesn't try). No user-defined
`@refine` aliases (predicates outside the four prelude shapes are
rejected with `TH0081`).

**Working example (0.6).**

```ts
// 0.6: refinement types as documentation primitives.

import type { Integer, Nat, Byte } from "./prelude";

// `Math.abs` overload: type-checker special-case returns Nat.
function magnitude(n: Integer): Nat {
  return Math.abs(n);
}

// `Array<T>.length: Nat` from the builtin-type-table.
function isEmpty<T>(arr: T[]): boolean {
  const n: Nat = arr.length;   // OK: arr.length is Nat
  return n === 0;
}

// `string.length: Nat` from the builtin-type-table.
function trimmedSize(s: string): Nat {
  return s.trim().length;
}

// Refined-typed signature documents what the function expects.
// Runtime is unchanged; this is just a sharper signature.
function setRetryBudget(retries: Nat, jitterMs: Byte): void {
  // body uses retries and jitterMs as ordinary numbers
}

// Out-of-range literal: caught at type-check time.
const PIXEL_LIMIT: Byte = 256;
//                        ^^^ TH0083: Literal value out of range for Byte (max 255)

// Negative literal into Nat: same machinery.
const COUNT: Nat = -1;
//                 ^^ TH0083: Literal value out of range for Nat (min 0)
```

**0.6-flavored expected-failure example (corpus).**

```ts
// 0.6: arithmetic on refined types not yet supported.
function double(b: Byte): Byte {
  // @ts-expect-error TS2322
  return b + b;
  //     ^^^^^ b + b: number; not assignable to Byte
}
```

This is *correctly rejected* in 0.6 — refined-type-preserving
arithmetic is the next version's job. The error code is `TS2322`
(plain TypeScript type mismatch), not `TH0080` (which doesn't
exist yet because there's no verifier).

---

### 0.7 — Refinement-aware arithmetic + narrowing

**What the user can do.** Static-table arithmetic preserves
refinement: `negate`, `double`, `bitAnd` all work and produce
refined results. The boundary pattern (`fromUnknown` with
`@throws`) lets users introduce refined values from external
`number` data. Mixed-refinement arithmetic (`Byte + Bit`) works
per the D17 table. The informational `TH0086` widening diagnostic
fires at sites that fall off the static table, alerting users
without blocking the build.

**Milestones.** B (static arithmetic table + `Severity` field) →
B.5 (mixed-refinement extension) → D0.5 (`@throws` non-returning
narrowing) → D1a (refinement-narrowing guard kind) → D1b
(boundary-pattern corpus + perf sweep) → F.7.

**What's still missing in 0.7.** No verification phase yet: when
arithmetic falls off the static table and the result flows into a
refined slot, the user gets `TH0086` *plus* a regular type-
mismatch error (just as in 0.6). The user can't yet write
`function add(a: Integer, b: Integer): Integer { return a + b; }`
and have the tool either prove or refute the refinement; the tool
just refuses the assignment. User-defined refinements still
rejected.

**Working example (0.7).**

```ts
// 0.7: arithmetic on the static table preserves refinement;
// narrowing recognizes prelude guards.

import type { Integer, Nat, Byte, Bit } from "./prelude";
import { isInteger, isByte } from "./prelude";

// Static table: Byte + Byte = Nat.
function sumBytes(a: Byte, b: Byte): Nat {
  return a + b;     // Byte + Byte: Nat per static table
}

// Static table: Bit & Bit = Bit (and similar for | ^ *).
function bitAnd(a: Bit, b: Bit): Bit {
  return a & b;
}

// Mixed-pair (D17): Byte + Bit = Nat.
function byteWithFlag(b: Byte, flag: Bit): Nat {
  return b + flag;
}

// Boundary pattern: external number → Integer via narrowing,
// throwing on failure. Requires D0.5 (post-throw narrowing).
/** @throws RangeError */
function asInteger(raw: number): Integer {
  if (!isInteger(raw)) throw new RangeError("not a safe integer");
  return raw;       // raw: Integer here, by D0.5 narrowing
}

// Math.abs hooks (already in 0.6).
function distance(start: Byte, end: Byte): Nat {
  const diff = end - start;       // Byte - Byte: Integer per static table
  return Math.abs(diff);          // Math.abs(Integer): Nat
}

// Off-static-table arithmetic: TH0086 fires (info), and the
// number result fails to assign back into a refined slot.
function tooMuch(a: Integer, b: Integer): Integer {
  // info[TH0086]: arithmetic on Integer widens to number
  //               at the `+` operator
  // error[TS2322]: number not assignable to Integer (on return)
  return a + b;
}
```

**Notes.**

- In 0.7, the `tooMuch` example above has the info+TS2322 shape.
  In 0.8, the same source produces `TH0086` + `TH0080` (the
  verifier was asked and refused). Tests track this transition
  explicitly (corpus example 8 in Part IV).
- D0.5's narrowing is what makes `asInteger` work: without it,
  the post-`throw` `return raw` would still see `raw: number`.

---

### 0.8 — Verification pipeline + obligations

**What the user can do.** Arithmetic outside the static table
gets *verified* rather than just refused. The `add(a, b)`
example correctly fails with `TH0080` (a counterexample exists
at the safe-integer boundary). Code paths that *can* be proven
safe — even when they're outside the static table — pass the
verifier and are accepted. The conditional-with-hypothesis
pattern (`offsetSign(n: Integer): Nat = n < 0 ? -n : n`) works
because the verifier sees the conditional hypothesis and can
discharge the obligation.

**Milestones.** C1 (obligation emitter + source-map registry) ‖
C2 (Lean subprocess driver) → C3 (stderr parser + diagnostic
surfacing) → C.5 (error-model lock + soundness review) → D2
(arithmetic obligations + `if h :` lowering + `thales_grind`) →
F.8.

**What's still missing in 0.8.** User-defined `@refine` aliases
still rejected (E hasn't shipped). Predicate sublanguage parser
isn't implemented; only the four prelude predicates are
recognized.

**Working example (0.8).**

```ts
// 0.8: verification pipeline ships. Obligations get checked.

import type { Integer, Nat, Byte } from "./prelude";

// Now possible because the verifier sees the ternary's hypothesis
// and discharges the obligation Integer → Nat under `n < 0`.
function offsetSign(n: Integer): Nat {
  return n < 0 ? -n : n;
}

// Now possible: 0 and 255 are Byte literals, b: Byte; both
// branches of the conditional return Byte values, which the
// verifier handles without an obligation.
function clampToByteOr(n: Integer, fallback: Byte): Byte {
  return n < 0 ? 0 : n > 255 ? 255 : fallback;
  // (the n > 255 branch needs verification; trivially discharged
  //  because 255: Byte and `n: Integer` is irrelevant)
}

// Off-table arithmetic that DOES verify: clamped sum.
// The verifier sees both operands are Byte (each ≤ 255),
// so the sum ≤ 510, well within Nat.
function safeSum(a: Byte, b: Byte): Nat {
  return a + b;     // already in 0.7; mentioned to contrast
}

// Off-table arithmetic that does NOT verify: TH0080 + TH0086.
function add(a: Integer, b: Integer): Integer {
  // info[TH0086]: arithmetic on Integer widens to number
  // error[TH0080]: refinement obligation not discharged
  //   = note: result flows into return slot of `add` (type Integer)
  //   = note: counterexample found at MAX_SAFE + MAX_SAFE
  return a + b;
}
```

**Notes.**

- The `offsetSign` example was tracer 3 in Part V; the PoC
  validated this discharge mechanism on `feat/thales-grind-poc`.
- The `add` example was a TS2322 in 0.7 and is now a TH0080 in
  0.8 — same source, different diagnostic, more useful error
  message (the verifier explains *why* the assignment is
  refused). Corpus example 8 captures this transition.

---

### 0.9 — User-defined refinements

**What the user can do.** Define their own `@refine` aliases.
Anything inside the predicate sublanguage from decision 5 +
decision 9 (named-constant atoms) compiles cleanly and
participates in the verification pipeline exactly like the
prelude types. The four prelude refinements remain the canonical
inhabitants but are no longer privileged in the parser — they're
just well-known instances of the user-extensible mechanism.

**Milestones.** E (predicate sublanguage parser + user-defined
`@refine` rejection of out-of-grammar predicates) → F.9.

**What's still missing in 0.9.** Disjunction (`||`) and negation
(`!`) in predicates still rejected. User-defined type guards
(`x is T`) still not supported. `as Integer` casts still
forbidden. `Math.floor`/`ceil`/etc. still return `number`.
Value-bound refinements like `IntegerLT<N>` still future. Array
bounds-checking still future.

**Working example (0.9).**

```ts
// 0.9: user-defined refinement types.

/** @refine x => Number.isInteger(x) && x >= 1 && x <= 65535 */
type Port = number;

function bind(port: Port): Server {
  return server.listen(port);
}

bind(80);     // OK: 80 is in [1, 65535]
bind(80000);  // TH0083: literal out of range for Port

// User predicate that's an alpha-rename of the prelude's Integer.
// The parser produces an AST that normalizes to the prelude shape;
// Thales recognizes it and treats `MyInt` as Integer.
/** @refine y => Number.isInteger(y) && y >= Number.MIN_SAFE_INTEGER && y <= Number.MAX_SAFE_INTEGER */
type MyInt = number;

const a: Integer = 42;
const b: MyInt = a;   // OK: AST equivalence

// User predicate using disjunction: rejected.
/** @refine x => x === 0 || x === 1 */
//                    ^^ TH0081: predicate not recognized
type MyBit = number;

// User predicate referencing a free variable: rejected.
/** @refine x => x > 0 && y > 0 */
//                       ^ TH0087: free variable `y`
type Bad = number;
```

**Notes.**

- D22's hand-off lands in this version: the hardcoded recognizers
  in A2 (for `@refine`) and D1a (for narrowing guards) are
  retired, replaced by the parser-produced AST. A regression test
  pins that user-written predicates whose AST normalizes to a
  prelude shape narrow exactly like the prelude version.

---

### Per-milestone detail

Detailed scope, layers touched, acceptance criteria, and effort
estimates for each milestone follow. Milestones are the same
units of work referenced in the version sections above; this
subsection is the per-issue reference.

### Milestone 0 — Refinement-types tour

**User value.** A curated tour of `.ts` files demonstrating every
type, lattice rule, narrowing pattern, arithmetic case, and
rejection scenario. Cheapest possible vertical-slice exercise:
walks every layer (declaration, lattice, literals, arithmetic,
narrowing, stdlib, rejections) without writing any compiler code.
If the design has a structural problem, it surfaces in a day.

**Layers touched.** None (documentation only). Files under
`docs/refinement-types-tour/`, each annotated with expected
compiler behavior.

**Acceptance.** Every `TH00XX` planned for 0.6 demonstrated with
the expected diagnostic noted in a comment; every corpus example
planned for A/B/D1/D2/E has a previewing fragment in the tour;
reviewer can read tour top-to-bottom in under 15 minutes.

**Estimated effort.** 1 day. Depends on nothing.

### Milestone A1 — Core lattice & literal checking

Split from original Milestone A.

**User value.** AST representation for refinement types; the
subtype lattice (`Bit <: Nat`, `Byte <: Nat`, `Nat <: Integer`,
all `<: number`) is in place; out-of-range literals fail at
compile time.

**Layers touched.**
- *Type-checker:* refinement-type AST representation; subtype
  lattice; static literal-range check.
- *Diagnostics:* `TH0083` (literal out of range), `TH0085`
  (multiple `@refine` on one alias).
- *Tests:* `Test/TypeCheck/RefinementLatticeTest.lean` covers
  transitivity, literal edges (-2^53+1, 0, 255, 256, 2^53-1,
  2^53).

**Estimated effort.** 2 days. Depends on Milestone 0.

### Milestone A2 — Prelude surface & overloads

Split from original Milestone A.

**User value.** Programmers can declare `Integer`/`Nat`/`Byte`/`Bit`
in function signatures, parameter lists, return types, and variable
declarations.

**Layers touched.**
- *Parser:* recognize `@refine` JSDoc on type aliases. Hardcoded
  recognition of the four prelude predicates (real parser ships
  in E; tracked as decision D22).
- *Stdlib hooks:* `Array.length: Nat`, `string.length: Nat`, four
  `Math.abs` overloads.
- *Prelude:* `Thales/TS/Prelude.d.ts` ships the four refined
  types.
- *Corpus:* a positive case using `Integer` in a signature; the
  TH0083 + TH0085 expected-failure fixtures.

**Estimated effort.** 2 days. Depends on A1.

### Milestone B — Static arithmetic table + diagnostic severity

**User value.** Basic arithmetic on small refinement types
preserves refinement: `negate`, `double`, `bitAnd`. The
informational `TH0086` widening diagnostic begins firing.

**Layers touched.**
- *Type-checker:* implement decision 6's static sound table.
- *Diagnostic infrastructure (NEW):* introduce `Severity` field
  (`error | info`) in `Thales/TypeCheck/Diagnostic.lean`. The
  field does not exist today (audit confirmed; Part VIII).
  Existing diagnostics become `error`. This is the slice that
  lands the severity concept.
- *Diagnostics:* `TH0086` (info, conservative trigger).
- *Corpus:* `negate`, `double`, `bitAnd` (positive). No
  obligations yet, so failure cases that depend on TH0080 are
  deferred to Milestone D2.

**Estimated effort.** 3 days. Depends on A2.

### Milestone B.5 — Mixed-refinement table extension

**New milestone, inserted 2026-05-06.**

**User value.** Mixed-refinement arithmetic produces useful
non-`number` types. `Byte + Bit` is `Nat`, etc. (per decision
D17).

**Layers touched.**
- *Type-checker:* extend the static table with the 12 mixed-pair
  entries from D17.
- *Tests:* extend `RefinementLatticeTest.lean` with the new rows.

**Acceptance.** All 12 mixed-pair entries from D17 typecheck per
the table. Off-table mixed pairs still fire `TH0086` per decision
6.

**Estimated effort.** ½ day. Depends on B.

### Milestone C1 — Obligation emitter + source-map registry

Split from original Milestone C (along with old C2, which was
re-merged then re-split as C2 below — see decision history).

**User value.** Internal: a working obligation-generation pipeline
for one minimal obligation kind (literal-into-refined-slot).

**Layers touched.**
- *Pipeline (NEW):* new phase 5 in `Thales/Main.lean`.
- *Verification emitter (NEW):* `Thales/Emit/Verify.lean`. Lowers
  one minimal obligation kind to verification-only Lean.
- *Source-map registry (NEW):* in-memory `Std.HashMap Nat ObligationInfo`,
  keyed by per-invocation `Nat` index. `ObligationInfo` shape per
  decision D20 (no `ts_file`; carries `value_span`, `slot_span`,
  `predicateText`, `contextDesc`).

**Estimated effort.** 3 days. Depends on B.5. (Can run parallel
to C2.)

### Milestone C2 — Lean subprocess driver

Split from original Milestone C.

**User value.** Internal: invoke `lake env lean` with timeout;
preserve the temp file via `--keep-verify-temp`.

**Layers touched.**
- *Subprocess driver (NEW):* `lake env lean` invocation with a
  per-call timeout (initial 30 s, configurable). Lean is invoked
  only when the registry is non-empty (skip path takes zero
  subprocess time per tracer 2's friction).
- *CLI:* `--keep-verify-temp` flag preserves the verify temp
  file + serializes the registry to JSON next to it.

**Estimated effort.** 2 days. Depends on B.5. (Can run parallel
to C1.)

### Milestone C3 — Stderr parser, diagnostic surfacing, edge-case fixtures

Split from original Milestone C.

**User value.** Internal: synthetic obligations end-to-end. TS-
positioned `TH0080` surfaces correctly.

**Layers touched.**
- *Stderr parser:* scan for `__thalesObligation_<n>` mentions;
  extract the index. Narrow substring-match (decision D19).
- *Diagnostic surfacing:* map indices to `ObligationInfo`; emit
  `TH0080` with predicate/context notes.
- *Edge-case fixtures:* synthetic failing-obligation, synthetic
  passing-obligation, multi-obligation (≥2 obligations, exactly
  one failing), conditional-with-hypothesis (pre-empts `if h :`
  lowering risk for D2), zero-refinement (no subprocess invoked),
  timeout.
- *Tests:* `Test/Emit/SourceMapRegistryTest.lean` (registry
  round-trip), `Test/Emit/VerifyDriverTest.lean` (mocked stderr,
  no subprocess).

**Estimated effort.** 2 days. Depends on C1, C2.

### Milestone C.5 — Error model lock + soundness review

**New milestone, inserted 2026-05-06.**

**User value.** Internal: every D19 failure mode is implemented
and tested; the soundness section of this spec is reviewed and
approved before any homomorphism axioms are committed.

**Layers touched.**
- Implementation pass on the D19 failure-mode table (each note
  prefix produces the right diagnostic).
- Review pass on Part III; no changes to Part III without
  matching changes here.

**Estimated effort.** 1 day. Depends on C3.

### Milestone D0.5 — `@throws` non-returning narrowing

**New milestone, inserted 2026-05-06.**

**User value.** Internal: post-`if` narrowing carries forward when
a branch terminated by `throw`/`return`. Prerequisite for D1's
`fromUnknown` corpus example. Audit (Part VIII) confirmed this is
genuinely missing today.

**Layers touched.**
- *Narrowing.lean:* approximately 30 lines of code per decision
  D21's scope.
- *Tests:* `Test/TypeCheck/NonReturningNarrowingTest.lean`.

**Estimated effort.** ½ – 1 day. Depends on B.5.

### Milestone D1a — Refinement narrowing guard kind

Split from original Milestone D1.

**User value.** Narrowing into refinement types via prelude guards
and inline patterns.

**Layers touched.**
- *Narrowing.lean:* refinement-narrowing guard kind, parallel to
  `typeofEquals`/`instanceOf`.
- *Recognition:* prelude guards by name (`isInteger`, `isNat`,
  `isByte`, `isBit`); inline predicate AST shapes for the four
  prelude predicates (string-match, replaced by parser-driven AST
  in E per decision D22).
- *Prelude:* `isInteger`/`isNat`/`isByte`/`isBit` declared with
  matching JS runtime bodies.

**Estimated effort.** 2 days. Depends on D0.5.

### Milestone D1b — Boundary-pattern corpus + perf sweep

Split from original Milestone D1.

**User value.** First observable user-visible refinement code:
`clamp`, `abs`, `fromUnknown` all work positively.

**Layers touched.**
- *Corpus:* `clamp(b: Byte): Byte`,
  `abs(n: Integer): Nat = Math.abs(n)`,
  `fromUnknown(raw: number): Integer` (boundary pattern with
  `@throws RangeError`).
- *Perf sweep:* `Test/PoC/` tracer timing `omega` discharge with
  1, 2, 4, 8, 16 stacked refinement-bound hypotheses; surfaces
  any super-linear cost growth before D2 commits to obligation
  generation.

**Estimated effort.** 2 days. Depends on D1a. The `fromUnknown`
example is the *first* corpus example added (so any residual
risk from D0.5 surfaces in week 1, not at end of milestone).

### Milestone D2 — Arithmetic obligations + `if h :` lowering + `thales_grind`

Kept atomic.

**User value.** The verifier catches arithmetic that doesn't
preserve refinement: `add(a: Integer, b: Integer): Integer`
correctly fails; `half(n: Integer): Integer` correctly fails.

**Layers touched.**
- *Type-checker:* arithmetic widening rules from decision 6 (the
  non-static-table cases generate obligations).
- *Verification emitter:* full obligation generation for
  arithmetic flowing into refined slots; `if h : ...` binding form
  for conditionals and ternaries.
- *Axioms:* the homomorphism axioms from Part III. Each annotated
  `-- AXIOM(thales): ...`.
- *thales_grind macro:* per Part VI.
- *Corpus:* `add`, `half` (both expect-error: TH0080 + TH0086).
- *Tests:* `Test/Emit/ObligationEmissionTest.lean` (golden Lean
  output), `Test/Emit/SoundnessTest.lean` (boundary-value pinning
  of `Float.ofInt`).

**Estimated effort.** 4 days. Depends on D1b, C.5.

### Milestone E — Predicate sublanguage parser + user-defined `@refine` rejection

Kept atomic.

**User value.** Predictable diagnostics when a user tries to
define their own `@refine` alias. User-defined refinements aren't
*accepted* in 0.6, but the error messages are clean rather than
"unhandled syntax." Sets up the post-0.6 generalization cleanly.
Retires the hardcoded recognizer per D22.

**Layers touched.**
- *Parser:* implement the full predicate sublanguage grammar from
  decision 5 (with decision 9's named-constant atoms).
- *Type-checker:* validate user `@refine` aliases — the prelude
  four match (special-cased by AST equivalence, not text);
  everything else yields `TH0081`.
- *Diagnostics:* `TH0081`, `TH0082`, `TH0084`, `TH0087`.
- *Regression:* the four prelude refinements still parse and
  behave per A1+A2; D22's hand-off invariant is pinned.
- *Corpus:* dedicated single-purpose examples for `TH0081`,
  `TH0082`, `TH0084`, `TH0087`.

**Estimated effort.** 3–5 days. Depends on D2.

### Milestone F.X — Per-version polish

Each version closes with a small polish milestone. Scope is
constant: update the doc files this version touched (per Appendix
A), add the CHANGELOG entry, run the tour validator (decision D23)
to confirm the tour annotations match reality for everything
shipped so far, and run a doc-vs-impl `git grep` consistency
sweep.

- **F.6** — 0.6 polish: `docs/subset.md` (refinement-types intro
  section), `docs/runtime.md` (transparency note), `docs/errors.md`
  (TH0083, TH0085 entries; new `Severity` concept stub),
  `docs/refinement-types-tour/` (tour landed and validated),
  CHANGELOG 0.6 entry. **½–1 day.**
- **F.7** — 0.7 polish: `docs/subset.md` (static table + mixed
  table + boundary pattern), `docs/errors.md` (TH0086 entry),
  CHANGELOG 0.7 entry. **½–1 day.**
- **F.8** — 0.8 polish: `docs/subset.md` (verification phase
  description), `docs/errors.md` (TH0080 entry + note prefix
  conventions from D19), `docs/refinement-soundness.md`
  promoted from this spec's Part III if not already, CHANGELOG
  0.8 entry. **1 day** (more text, since this is the
  architecturally novel version).
- **F.9** — 0.9 polish: `docs/subset.md` (predicate sublanguage
  reference), `docs/errors.md` (TH0081, TH0082, TH0084, TH0087),
  `docs/future.md` (move "refinement types" out of Arc 2 into
  "shipped"), CHANGELOG 0.9 entry. **½–1 day.**

### Total effort across all four versions

~28–33 working days (was 26–31 in the single-version plan; the
extra ~2 days are the per-version F.X polish overhead).
Per-version subtotals:

| Version | Milestones                                  | Subtotal     |
| ------- | ------------------------------------------- | ------------ |
| 0.6     | M0, A1, A2, F.6                             | 5½–6 days    |
| 0.7     | B, B.5, D0.5, D1a, D1b, F.7                 | 10½–12 days  |
| 0.8     | C1, C2, C3, C.5, D2, F.8                    | 13–15 days   |
| 0.9     | E, F.9                                      | 3½–6 days    |

### Milestone summary table

| Milestone | Ships in | User value                                              | Highest-risk question answered                          | Effort |
| --------- | -------- | ------------------------------------------------------- | ------------------------------------------------------- | ------ |
| M0        | 0.6      | Tour                                                    | Are there structural design holes?                      | 1d     |
| A1        | 0.6      | Lattice & literal range                                 | Subtype lattice clean?                                  | 2d     |
| A2        | 0.6      | Prelude + overloads                                     | Builtin-type-table conflicts?                           | 2d     |
| F.6       | 0.6      | Polish + tour validator                                 | Tour-vs-impl agreement                                  | ½–1d   |
| B         | 0.7      | Static table + severity                                 | Severity-aware diagnostic plumbing                      | 3d     |
| B.5       | 0.7      | Mixed-pair table                                        | Mixed-refinement coherent?                              | ½d     |
| D0.5      | 0.7      | `@throws` non-returning narrowing                       | Boundary pattern unblocked?                             | ½–1d   |
| D1a       | 0.7      | Refinement narrowing guard kind                         | Narrowing infrastructure?                               | 2d     |
| D1b       | 0.7      | Positive corpus + perf sweep                            | `omega` cost growth bounded?                            | 2d     |
| F.7       | 0.7      | Polish                                                  | Doc-vs-impl drift                                       | ½–1d   |
| C1        | 0.8      | Obligation emitter + registry                           | Source-map round-trips?                                 | 3d     |
| C2        | 0.8      | Subprocess driver                                       | Subprocess plumbing solid?                              | 2d     |
| C3        | 0.8      | Stderr parsing + TH0080                                 | Architecture viable?                                    | 2d     |
| C.5       | 0.8      | Error model + soundness lock                            | All failure modes handled?                              | 1d     |
| D2        | 0.8      | Arithmetic obligations + `thales_grind`                 | Discharger handles real arithmetic?                     | 4d     |
| F.8       | 0.8      | Polish (incl. soundness doc promotion)                  | Trust-base auditable                                    | 1d     |
| E         | 0.9      | Predicate parser + user-defined rejection               | Grammar implementable?                                  | 3–5d   |
| F.9       | 0.9      | Polish                                                  | Doc-vs-impl drift                                       | ½–1d   |

---

## Part VIII — Codebase audit (2026-05-06)

Audit performed against `main` to identify pre-conditions the
roadmap depends on.

### Diagnostic severity field — does not exist

`Thales/TypeCheck/Diagnostic.lean` does not currently carry a
`Severity` field. `grep -n "Severity\|severity"` returns no hits.
Milestone B's "introduce `Severity`" is genuine new infrastructure.

### Throw-as-non-returning narrowing — does not exist

`Thales/TypeCheck/Narrowing.lean` (376 lines) handles narrowing
inside `if` branches but has no notion of branches that don't
continue to post-block code.

`Thales/TypeCheck/Check.lean` lines 359–388 (the `ifStmt`
elaborator) narrows inside each branch via `withScope`, then
**unconditionally reverts** to the pre-branch bindings via
`restoreAssignmentState` after the branches exit. There is no
inspection of whether either branch was terminated by a `throw`
or `return`.

This confirms decision D21's premise: the boundary pattern
(`if (!Number.isInteger(raw)) throw ...; return raw;`) cannot
type-check with current code, because `raw` reverts to `number`
post-`if`. Milestone D0.5 is genuinely required.

### Throws machinery — exists, but for a different purpose

`Thales/TypeCheck/Check.lean` line 470 has `.throwStmt _ expr`
handling, and the `collectUncaughtThrowEvents` function (line 567+)
walks the AST for `@throws`-annotation inference (TH0060). This
is "does this function's body throw something?" — not "is this
branch unreachable for the purposes of post-block narrowing?"
Milestone D0.5 introduces the latter as a separate, focused pass.

### PoC artifacts on `feat/thales-grind-poc`

- `Test/PoC/RefinementGrind.lean` — the validated tracer set; 6
  theorems + 4 examples; ~0.43 s warm compile time.
- `Test/PoC/FINDINGS.md` — the validation summary; folded into
  Part VI.
- The three homomorphism axioms (`Float.ofInt_neg`, `_lt`, `_le`)
  are defined locally in the PoC file. Milestone D2 moves them
  into `Thales/Emit/Verify.lean` (or sibling) with the
  `-- AXIOM(thales): ...` annotation convention.

---

## Part IX — Out of scope (per version)

Each version ships with a tighter scope than the next; the cuts
below identify what's *not* in each version, so reviewers can
calibrate expectations.

### Out of scope for 0.6

- **No arithmetic preservation.** Even `negate(n: Integer): Integer`
  doesn't work in 0.6 — the static table is 0.7 work. Result of
  any arithmetic on refined values is `number`.
- **No narrowing.** `if (isInteger(x)) ...` is not understood;
  `x` stays `number` inside the branch.
- **No verification phase.** No TH0080. Refinement violations
  surface only as out-of-range literals (TH0083), multiple
  `@refine` (TH0085), or regular type-mismatch errors when refined
  values can't be assigned to refined slots.
- **No user-defined `@refine` aliases.** Predicates outside the
  four prelude shapes are rejected (TH0081 stub; full machinery
  in 0.9).
- **No mixed-refinement subtype interactions** at runtime —
  `Bit <: Nat` is a typing fact, not exercised by code.

### Out of scope for 0.7

- **No verification phase yet.** TH0086 fires informationally on
  off-table arithmetic, but the result still can't flow back into
  a refined slot (regular TS2322 type error). 0.8 lifts this.
- Same scope locks as 0.6 for user-defined refinements,
  bounds-checking, etc.

### Out of scope for 0.8

- **No user-defined refinements** (still 0.9 work). The
  hardcoded predicate recognizers from A2 and D1a are still in
  place.
- **No batched verification.** One `thales` invocation processes
  one TS file (decision D20).
- **No embedded Lean.** 0.8 keeps the shell-out-to-`lake env lean`
  pattern; in-process Lean is post-0.9.

### Out of scope for 0.9 (and the whole 0.6 → 0.9 ladder)

These remain *post-0.9* features even after the full ladder
ships. Each is a deliberate scope lock that prevents the basic
refinement-types epic from accreting unrelated work.

- **No user-defined type guards (`x is T`).** A bigger feature
  that intersects every narrowing concern in TS, not just
  refinement types.
- **No `as Integer` casts.** Unchecked refinement assertions
  defeat the verification framework.
- **No `Math.floor`/`ceil`/`trunc`/`round` refinement.** They
  return `number` because of NaN/Infinity for non-finite input.
- **No array bounds-checking refinements.** Dependent
  length-tracking is a separate "non-empty array / safe-index"
  milestone.
- **No disjunction (`||`) or negation (`!`) in predicates.**
- **No `@requires`/`@ensures` proof annotations** — separate
  Arc 2 milestone.
- **No runtime emission of `@refine` predicates.** Compile-time
  artifact; runtime validation libraries (Zod and similar) remain
  a separate concern.
- **No closure of full-range `Integer` / `Nat` arithmetic.** The
  static sound table is intentionally small; off-table arithmetic
  widens. Value-bound refinements (e.g., `IntegerLT<N>`) that
  would let users prove tighter ranges are a future feature.
- **No general TS function-overload resolution.** Decision 11
  uses hardcoded special cases per prelude type.
- **No batched verification.** One `thales` invocation processes
  one TS file; multi-file batching is future work.
- **No embedded Lean.** Shell-out to `lake env lean` remains the
  verifier-invocation model.

---

## Part X — Open questions

These are the remaining genuinely-unsettled items as of 2026-05-06.
Each should resolve before its containing milestone starts.

1. **`Float.ofInt_sub` direction.** The PoC ships `Float.ofInt_neg`
   in the form `-(Float.ofInt n) = Float.ofInt (-n)` (rewrite
   inward). Part III ships `Float.ofInt_sub` in the form
   `Float.ofInt a - Float.ofInt b = Float.ofInt (a - b)` (also
   rewrite inward). Direction must match what the `simp` ruleset
   in `thales_grind` actually wants — verify against a real
   obligation in D2 before the axiom set freezes.

2. **`if h :` lowering edge cases.** The C3 fixture covers an
   obligation living inside a conditional that *uses* the
   hypothesis. D2 must extend this to ternaries and nested
   conditionals. The PoC validated the simple case; nested
   stacking is not pre-validated. If the lowering is harder than
   expected, D2 may grow.

3. **Tour validator implementation choice.** D23 defers between
   `scripts/validate-tour.js` (TS-aware) and a Lean-side test.
   The choice depends on what's easier to keep in sync with the
   actual diagnostic output format. Decide during F.

4. **Per-obligation timeout policy.** Initial 30s is from decision
   7. Whether to make this user-configurable at the CLI in 0.6, or
   defer to 0.7, is open. Default to "not configurable in 0.6;
   stretch goal."

5. **Documentation of mixed-refinement subtraction/multiplication.**
   D17 explicitly enumerates addition mixed-pair rows. The
   subtraction and multiplication generalizations are stated only
   in prose. Before B.5 starts, decide whether to enumerate
   subtraction and multiplication mixed-pair rows in the table or
   leave them implicit. Recommend: enumerate them for clarity,
   even if the body-of-code reduces to "join the result types via
   the lattice."

6. **Negative-zero handling.** `Number.isInteger(-0)` returns
   `true` in JavaScript, so `-0` is in the JS-side `Integer`
   predicate. Lean's `Float` keeps `-0.0` distinct from `+0.0`
   under propositional equality (different bit patterns; no
   `DecidableEq` instance; `Float.ofInt 0 = -0.0` does not hold
   by `rfl`), even though IEEE `==` treats them as equal.

   **Implication: the PoC's `Float.ofInt_neg` axiom**

   ```lean
   axiom Float.ofInt_neg (n : Int) :
       -(Float.ofInt n) = Float.ofInt (-n)
   ```

   **is technically unsound at `n = 0`** — the axiom claims
   `-0.0 = +0.0` propositionally, which is false in Lean. The
   PoC doesn't trip the bug because every use occurs with a
   hypothesis like `n_int < 0` in scope, but the axiom-as-stated
   is a latent unsoundness in the trust base.

   **Decision deferred to Milestone D2 / 0.8.** This question
   does not block 0.6 or 0.7 (neither has a verifier). When 0.8
   implementation begins, pick one of:

   - **Domain-restrict the axiom** — `Float.ofInt_neg (n : Int)
     (h : n ≠ 0) : ...`. Smallest change; obligation emitter
     threads the `n ≠ 0` precondition from surrounding
     hypotheses.
   - **Type-system rename** — introduce a `TSInteger` type
     (the verifier-side Lean reflection of the JS `Integer`
     concept, distinct from Lean's `Int`) whose equality is
     defined to match the JS view. Restates axioms cleanly
     without per-case domain restrictions. Larger change but
     cleaner naming.
   - **Some hybrid** — the right answer depends on what feels
     natural once D2 is being implemented and the obligation
     shapes are concrete in front of us.

   **Action items, regardless of choice:**
   - In D2, add `Test/Emit/NegativeZeroSoundness.lean` that
     derives `False` from the existing `Float.ofInt_neg` at
     `n = 0`, then confirms the chosen fix closes it.
   - Add a corpus example exercising `negate(0)` and `negate(-0)`
     to verify the runtime/verifier alignment end-to-end.

---

## Part XI — Prelude documentation conventions

`Thales/TS/Prelude.d.ts` is the source of truth for *both* the
refinement type aliases *and* the refinement-aware overloads of
stdlib functions. Adding a new prelude refinement (in any version,
including post-0.9) means editing this one file: declare the type
alias, declare any overloads that participate in
refinement-aware behavior, and add a short JSDoc explaining the
rationale. The file is parsed by `tsc` (which sees only the base
`number` type) and by Thales (which honors `@refine` and the
overload signatures); the two readings are consistent because
overloads' refined return types are erased to `number` at runtime.

### Why this works

`tsc` and Thales agree on what `Integer` *is* (it's `number`) but
disagree on what it *means*. From `tsc`'s perspective, all the
following overloads collapse to `Math.abs(n: number): number`:

```ts
declare namespace Math {
  function abs(n: Integer): Nat;
  function abs(n: Nat): Nat;
  function abs(n: Byte): Byte;
  function abs(n: Bit): Bit;
  function abs(n: number): number;
}
```

Thales sees these as four distinct, ordered overload arms, picks
the most specific match per the subtype lattice (Bit <: Byte? — no:
Bit <: Nat, Byte <: Nat, Nat <: Integer), and emits the refined
return type. At runtime, the result is whatever the JavaScript
`Math.abs` returns; the type-level distinction is erased.

This convention extends naturally to other stdlib functions and
to user-facing libraries that ship `.d.ts` augmentations.

### Conventions per kind of declaration

#### Type aliases

Every prelude refinement type is declared exactly once:

```ts
/** @refine x => Number.isInteger(x) && x >= Number.MIN_SAFE_INTEGER && x <= Number.MAX_SAFE_INTEGER */
type Integer = number;

/** @refine x => x >= 0 */
type Nat = Integer;

/** @refine x => x <= 255 */
type Byte = Nat;

/** @refine x => x < 2 */
type Bit = Nat;
```

The chained-base-type pattern (`Nat = Integer`, etc.) is the L4
composition rule from decision 4. The effective predicate is the
conjunction along the chain.

#### Refinement-aware overloads

Overloads are listed from most-specific to least-specific. Thales
matches the first one whose argument type the call's argument is
assignable to under the refinement lattice; the trailing
`(n: number): number` overload is the catch-all for unrefined
inputs and is what `tsc` actually uses.

```ts
declare namespace Math {
  function abs(n: Bit): Bit;
  function abs(n: Byte): Byte;
  function abs(n: Nat): Nat;
  function abs(n: Integer): Nat;
  function abs(n: number): number;
}
```

Note the `(n: Integer): Nat` row — the "absolute value of any
safe integer is a non-negative safe integer" claim. This is the
non-trivial overload; the others are identity-on-refinement.

#### Built-in property overloads

Some refinements live on built-in types' properties (e.g.,
`Array<T>.length`). These are not expressible as TS overloads
because property type isn't a function type. Thales handles them
as special cases in the type-checker's builtin-type-table; the
prelude file documents them via interface augmentation:

```ts
interface Array<T> {
  /** Refinement-aware: array length is always a Nat. */
  readonly length: Nat;
}

interface String {
  /** Refinement-aware: string length is always a Nat. */
  readonly length: Nat;
}
```

The JSDoc serves the human reader; the type-checker's builtin
table is the authoritative implementation.

#### Prelude helper guards (added in 0.7)

Each prelude refinement ships a runtime-realizable guard whose
return value is exactly the refinement's predicate. The guards
have full JS implementations (not just `declare` statements) so
that the runtime behavior matches the type-checker's
interpretation.

**Note on `-0`:** the runtime guards do *not* reject `-0`.
Negative zero is a real JavaScript value and `Number.isInteger(-0)`
is `true`; pretending it isn't would lead to surprises. The
verifier-side handling of `-0` is deferred to Milestone D2 / 0.8
(see Part X open question 6). The guard implementations are
the literal predicate translation:

```ts
/** True iff `n` is a JS-safe integer.
 *  Type-checker recognizes this by name as a narrowing guard for `Integer`. */
export function isInteger(n: number): boolean {
  return Number.isInteger(n)
      && n >= Number.MIN_SAFE_INTEGER
      && n <= Number.MAX_SAFE_INTEGER;
}

/** True iff `n` is a non-negative JS-safe integer.
 *  Narrowing guard for `Nat`. */
export function isNat(n: number): boolean {
  return isInteger(n) && n >= 0;
}

/** Narrowing guard for `Byte`. */
export function isByte(n: number): boolean {
  return isNat(n) && n <= 255;
}

/** Narrowing guard for `Bit`. */
export function isBit(n: number): boolean {
  return isNat(n) && n < 2;
}
```

The naming convention is `is<TypeName>` for every prelude
refinement. The type-checker recognizes the guard by name in
0.7+ (D1a); the parser-driven recognizer in 0.9+ (E + D22)
recognizes guards whose body's effective predicate matches the
refinement's, regardless of name.

### Adding a new prelude refinement (post-0.9 work or future versions)

Suppose a future version adds `Port` (TCP/UDP port, 1–65535) as
a prelude refinement. The change to `Prelude.d.ts`:

```ts
/** @refine x => Number.isInteger(x) && x >= 1 && x <= 65535 */
type Port = number;

declare namespace Math {
  // No new abs overload — Port is a subtype of Nat, so the
  // existing (n: Nat): Nat row covers Math.abs(p: Port).
  // (And Math.abs of a Port can technically be larger than Nat
  //  bounds — wait, no, |port| ≤ 65535 ≤ MAX_SAFE so it's fine.)
}

// Standalone library functions for ports get their overloads.
export declare function bindServer(port: Port): Server;
export declare function bindServer(port: number): Server;

// Narrowing guard.
export function isPort(n: number): boolean {
  return isInteger(n) && n >= 1 && n <= 65535;
}
```

That single file change — type alias + overloads + guard — is the
complete contract. The type-checker's hardcoded special-cases for
`Port` (e.g., literal-range check) come for free from the
generic refinement machinery once the alias is recognized.

### Working examples of the `Math.abs`-shape convention

Some stdlib functions where refinement-aware overloads pull their
weight, with sketches of the overload signatures (post-0.9
candidates, not in scope for 0.6 → 0.9):

```ts
// Math.min / Math.max preserve refinement when both args agree.
declare namespace Math {
  function min(a: Bit, b: Bit): Bit;
  function min(a: Byte, b: Byte): Byte;
  function min(a: Nat, b: Nat): Nat;
  function min(a: Integer, b: Integer): Integer;
  function min(...values: number[]): number;
  // (max symmetric)
}

// Number.parseInt: returns Integer | NaN. Without union types
// in refinements (0.9 still doesn't have these), the most we
// can say is `number`.
declare interface NumberConstructor {
  parseInt(s: string, radix?: number): number;
}
```

The `parseInt` case illustrates a convention boundary: when a
refinement-aware return type would require union refinements
(`Integer | NaN`), and union refinements aren't in the language,
the convention is to leave the return type unrefined. This keeps
the prelude file honest about what Thales can actually verify.

### Shadowing and namespacing

Thales's prelude is a **module**, not an ambient global. Users
explicitly `import` the types and guards they want; types not
imported are not in scope. Mirroring tsc:

- A user who does not import the prelude can declare their own
  `Integer`, `Nat`, `Byte`, `Bit` freely — no conflict, since
  the prelude names aren't in scope.
- A user who imports a prelude name and tries to redeclare it
  at module scope gets a `tsc` error (TS2440 "Import
  declaration conflicts with local declaration of 'Integer'.").
  Thales does not need a separate diagnostic for this; the
  conformance contract guarantees `tsc`'s error fires first.
- A user who wants both their own `Integer` and the prelude's
  uses an `import as` rename, which `tsc` accepts cleanly:

  ```ts
  import { Integer as PreludeInteger } from "@thales/prelude";
  type Integer = string;          // user's own; no conflict
  ```

- Inner-scope shadowing always works (TS scoping rule):

  ```ts
  import { Integer } from "@thales/prelude";

  function localOverride(): string {
    type Integer = string;        // shadows the import inside this scope
    const x: Integer = "hello";
    return x;
  }
  ```

Empirical confirmation (typescript@6.0.2): the four patterns
above produce, respectively, no error, TS2440, no error, no
error.

#### Why no sigil

A natural-seeming alternative would be to claim a sigil for
prelude types, e.g. `%Integer`, so that user-defined `Integer`
and Thales-defined `%Integer` could coexist in the same scope
without conflict. We considered this and rejected it for two
reasons:

1. **`%` is not a valid TypeScript identifier character.** A
   file containing `%Integer` would fail `tsc` parsing, breaking
   the conformance contract that says every Thales-accepted file
   must `tsc`-check cleanly.
2. **The namespacing problem is already solved.** ES module
   imports + `import as` give users complete control over which
   names enter their scope, with no Thales-specific machinery.
   Inventing a sigil to solve a problem the language already
   solves is gratuitous.

A user who wants short names without an `import as` can put
their own definitions in their own module and not import the
prelude there:

```ts
// my-domain-types.ts — no prelude import
export type Integer = bigint;     // my domain wants arbitrary-precision
export type Nat = bigint;

// rest-of-app.ts — uses my types, not the prelude
import type { Integer, Nat } from "./my-domain-types";
```

#### How Thales handles a user-shadowed prelude type

When a user-defined type uses a name from the prelude (in
whatever scope: module-level via no-import, module-level via
`import as`, or function-local via shadowing), Thales treats the
user's type as the in-scope reference. The `@refine` machinery
applies only if the user's type carries its own `@refine`
annotation; without one, Thales sees an ordinary type alias and
applies no refinement reasoning to it. This is desirable — a
user who shadows `Integer` to mean `bigint` (or `string`, or
anything else) gets exactly the type they declared, with no
interference.

A user who shadows a prelude type *and* attaches a different
`@refine` predicate gets a different refinement type. Same
machinery, different predicate; no special case needed.

### Tour file linkage

The Milestone 0 tour (`docs/refinement-types-tour/`) includes a
file that demonstrates each prelude type's surface and overload
behavior — this file is added to in lockstep with `Prelude.d.ts`
when a new refinement ships. The tour validator (decision D23)
ensures the demonstrated behavior matches reality.

---

## Appendix A — Documentation file changes per version

These changes land incrementally during each version's milestones
rather than all at the end. The per-version `F.X` polish
milestone is consistency-sweep + CHANGELOG, not first-time
drafting.

### 0.6 doc changes

- **`docs/subset.md`** — new "Refinement types" section
  introducing the four prelude types, the subtype lattice, and
  the literal-range check. Does *not* yet describe arithmetic or
  narrowing (those land in 0.7).
- **`docs/errors.md`** — entries for `TH0083` (literal out of
  range), `TH0085` (multiple `@refine`). Stub for the new
  `Severity` field concept (no `info` codes ship in 0.6 yet, but
  the field is reserved).
- **`docs/runtime.md`** — note that the four refinement types are
  runtime-transparent (no runtime helpers); note `Math.abs`
  overload behavior at the type level only.
- **`docs/future.md`** — note that "refinement types" is in
  progress, with the version ladder linked from the entry.
- **`docs/refinement-types-tour/`** — Milestone 0's annotated
  tour files (only the chapters demonstrating 0.6 features need
  to be truthful; later chapters are forward-looking and tagged
  `[ships in: 0.X]`).
- **`Thales/TS/Prelude.d.ts`** — add the four type aliases per
  Part XI's conventions and the `Math.abs` overloads. No prelude
  guards yet (those land in 0.7).
- **`examples/`** — example 5 (`abs`), example 7 (TH0083 literal
  failure). Plus a 0.6-specific failure example showing
  `function double(b: Byte): Byte { return b + b; }` failing
  with TS2322 (no static table yet).
- **`CHANGELOG`** — "0.6: refinement types as documentation
  primitives. `Integer`, `Nat`, `Byte`, `Bit` declarable in
  signatures; `Math.abs`, `Array.length`, `string.length`
  refinement-aware; out-of-range literal check (TH0083);
  diagnostic severity field added (info codes reserved for 0.7+)."

### 0.7 doc changes

- **`docs/subset.md`** — extend the Refinement types section with
  the static arithmetic table (decision 6 + D17), the prelude
  guards, the boundary pattern, and the inline-predicate
  narrowing.
- **`docs/errors.md`** — `TH0086` entry; "diagnostic severity"
  concept now shipping with its first info code.
- **`docs/refinement-types-tour/`** — chapters 04 (arithmetic),
  06 (narrowing), 07 (boundary), 08 (clamp) become live.
- **`Thales/TS/Prelude.d.ts`** — add the four `is<Type>` guards
  (with full JS implementations).
- **`examples/`** — examples 1 (`negate`), 2 (`double`), 3
  (`bitAnd`), 4 (`clamp`), 6 (`fromUnknown`). Example 8 ships in
  its 0.7-flavored variant (TS2322 + TH0086).
- **`CHANGELOG`** — "0.7: refinement-aware arithmetic on the
  static sound table; mixed-refinement extension; narrowing for
  prelude guards and inline predicates; boundary pattern via
  `@throws`. New informational diagnostic TH0086 for arithmetic
  widening."

### 0.8 doc changes

- **`docs/subset.md`** — add the verification phase description.
- **`docs/errors.md`** — `TH0080` entry with the D19 note-prefix
  table (timeout, internal:..., verifier killed, etc.).
- **`docs/refinement-soundness.md`** — promote Part III of this
  spec into a top-level `docs/` file. The audit-ready trust
  base story belongs alongside the user-facing docs once 0.8
  ships, not buried in the working spec.
- **`docs/refinement-types-tour/`** — chapter 05 (arithmetic
  widening) and the verifier-failure annotations become live.
- **`Thales/TS/Prelude.d.ts`** — no new types in 0.8.
- **`examples/`** — examples 8 (`add`), 9 (`half`) ship in their
  TH0080 form (replaces the 0.7-flavored TS2322 variant of 8).
- **`CHANGELOG`** — "0.8: verification pipeline ships. Refinement
  obligations checked via Lean subprocess. New error TH0080 with
  structured notes for refutation, timeout, and internal failure
  modes. Per-file source-map registry; `--keep-verify-temp` flag."

### 0.9 doc changes

- **`docs/subset.md`** — predicate sublanguage grammar reference
  (decision 5 + 9).
- **`docs/errors.md`** — `TH0081`, `TH0082`, `TH0084`, `TH0087`
  entries.
- **`docs/future.md`** — move "refinement types" out of Arc 2's
  open list into a "shipped in 0.6 → 0.9" section. Add
  value-bound refinements (`IntegerLT<N>`), array bounds, etc.,
  to a new "post-0.9 refinement-types growth path" subsection.
- **`docs/refinement-types-tour/`** — chapter 10 (user-defined,
  rejection demos) becomes live.
- **`Thales/TS/Prelude.d.ts`** — no surface changes; the parser
  is what changed.
- **`examples/`** — TH0081, TH0082, TH0084, TH0087 single-purpose
  failure examples.
- **`CHANGELOG`** — "0.9: user-defined `@refine` aliases. Full
  predicate sublanguage parser. The four prelude refinements
  remain canonical but are no longer privileged; user-written
  predicates equivalent to a prelude one are recognized as
  such."

---

## Appendix B — Glossary

- **L1 / L2 / L3** — three considered lowering strategies for
  refinement types. L1: lower `Integer` to Lean `Int` directly.
  L2: a `Float` subtype with proofs over `Float`. L3: runtime
  unchanged (`Float`), reflect to `Int` for verification. We use
  L3.
- **`Float.IsSafeInteger`** — Lean predicate
  `∃ n : Int, x = Float.ofInt n ∧ minSafe ≤ n ∧ n ≤ maxSafe`. The
  reflection bridge between `Float` and `Int`.
- **`thales_grind`** — Lean tactic macro:
  `simp only [<axioms>] at *; unfold minSafe maxSafe at *; omega`.
  Not in Lean's stdlib; supplied by Thales.
- **Obligation** — a Lean proposition whose validity Thales
  delegates to `lake env lean`. Each is named
  `__thalesObligation_<n>` and tracked in the source-map registry.
- **Static sound table** — the small table of arithmetic forms
  whose result-type is provable from operand bounds alone, no
  obligation needed (decision 6 + D17).
- **TH-code** — Thales-internal diagnostic code, e.g. `TH0080`.
  Range `TH0080`–`TH0089` is reserved for refinement types.
- **`@refine`** — JSDoc directive on a TS type alias carrying its
  predicate.
- **MIN_SAFE / MAX_SAFE** — `±(2^53 − 1)` =
  `±9007199254740991`. The boundaries of JavaScript's
  safe-integer range.
- **`AXIOM(thales)`** — comment marker on every homomorphism
  axiom, used by `git grep` to enumerate the trust base.
- **Boundary pattern** — the `fromUnknown(raw: number): Integer`
  shape: external `number` checked at a function boundary,
  narrowed to refinement type, throw on failure. The killer
  feature of refinement types in practice.
