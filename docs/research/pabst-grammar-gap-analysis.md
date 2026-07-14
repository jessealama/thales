# Gap analysis: Pabst grammar productions vs Thales Lean lowering

Research note for issue #96 (parent #93). Production-by-production analysis
of Pabst's normative grammar (`docs/grammar.ebnf`, pabst 0.13.0) against what
Thales can lower to Lean today. Pabst paths are relative to the pabst
checkout; Thales paths are relative to this repository. Date: 2026-07-14.

## Reading the classification

Thales today emits **no theorems at all** — the emitter produces `def`s and
runtime code only (grep of `Thales/Emit/` finds `theorem` only in the
reserved-keyword list, `Thales/Emit/LeanSyntax.lean:276`; the only sketch of
obligation emission is in the spec `docs/specs/basic-refinement-types.md`,
the `theorem __thalesObligation_0` example). So in the strictest sense
*every* production "needs widening": a theorem-statement emission surface has
to exist first. That surface is a single shared prerequisite, not a
per-production gap, so the classification below assumes it and asks the
useful question: **once Thales can emit a `theorem` header, does its existing
type and expression lowering give the production a faithful Lean meaning?**

- **translatable today** — existing Thales lowering (types, operators,
  runtime) already denotes the construct; the theorem scaffold is the only
  missing piece.
- **needs subset widening** — new but well-understood emission or checking
  machinery is required; no semantic decision blocks it.
- **thorny, needs decision** — a semantic mismatch between the JS meaning
  and any candidate Lean meaning must be resolved by a design decision
  before implementation.

## Summary table

| # | Production (grammar.ebnf) | Classification | Lean lowering sketch |
|---|---------------------------|----------------|----------------------|
| 1 | `property` (:18) | needs subset widening | `theorem <fn>.<name> : ∀ …, ⟦formula⟧ = true` — new emission surface |
| 2 | `prefix`, `FORALL` (:24–29) | translatable today | Lean `∀`; ∃ never reaches Thales (pabst rejects it) |
| 3 | `binder-group`, `var-name` (:31–34) | translatable today | `(x y : τ)` is literally Lean binder syntax; keyword-collision rename needed |
| 4a | `domain` = `int` (:35) | translatable today | prelude `Integer` = `{x : Float // x.isInteger ∧ \|x\| ≤ 2^53−1}` |
| 4b | `domain` = `nat` (:35) | translatable today | prelude `Natural` (Float subtype), **not** Lean `Nat` |
| 4c | `domain` = `number` (:35) | thorny, needs decision | `Float` — IEEE double; essentially nothing is provable about Lean `Float` arithmetic |
| 4d | `domain` = `boolean` (:35) | translatable today | `Bool` |
| 4e | `domain` = `string` (:35) | translatable today | `String` (UTF-16 vs scalar caveat) |
| 4f | `domain` = `bigint` (:35) | translatable today | `Int` (termination caveat for recursive islands) |
| 5 | `constraint`, `MEMBER` (:37–41) | needs subset widening | constraint → hypothesis or `Subtype` on the binder |
| 6 | `regex-literal` guard (:43–49) | thorny, needs decision | `lean-regex` is already a pinned dependency but unused; three regex dialects must be reconciled |
| 7 | `interval`, `endpoint`, `INFINITE` (:51–63) | needs subset widening (number-domain corners thorny) | int/nat/bigint: closed integer bounds as hypotheses; number: double-ordering corner cases |
| 8 | `formula` connectives ∧ ∨ ¬ → ↔ (:69–91) | translatable today | `&&`/`\|\|`/`!`/`bimp`-style Bool image, or Prop connectives over `= true` atoms |
| 9 | root implication ≙ `fc.pre` (:72–77) | translatable today | both fc.pre discard and material `→` collapse to hypotheses of the theorem |
| 10 | `atom`, `EQUATION` ≡/≢ (:95–102) | thorny for `number`, translatable otherwise | `Object.is` ≠ Lean `Float ==` on NaN and −0; needs a `sameValue` runtime def |
| 11 | `island` (:103–106) | needs subset widening (per island, gated today) | island = ordinary Thales expression; existing TH checks are the gate |
| 12 | atom side conditions / hygiene (:108–117) | translatable today | Thales's static checks subsume pabst's runtime hygiene checks |

Counts: **10 translatable today · 4 need subset widening · 3 thorny**
(counting 4c, 6, 10 as the thorny set; the number-interval corner in 7 folds
into the same decision as 4c).

---

## 1. `property ::= prefix "{" formula "}"` — needs subset widening

**Pabst.** `src/prefix-parser.ts:21-71` (`parsePrefix`) splits the annotation
into binders and body; `src/emit.ts:78-100` (`emitProp`) assembles the
generated test: `test.prop([<arbs>], …)(<name>, (<vars>) => { fc.pre(…);
const __r = (<body>); return __r; })`.

**Thales.** No theorem/property emission exists (`Thales/Emit/` has none;
the reserved-word list at `Thales/Emit/LeanSyntax.lean:276` is the only hit
for `theorem`). The vision doc already names this exact destination:
`docs/future.md:85-92` — `@requires`/`@ensures` with **dual discharge**
(fast-check run *and* Lean escalation). Pabst is the fast-check half; the
Lean half is this gap.

**Lowering sketch.** For `@ensures{nonzero} forall (x: bigint) (y: number)
{ Number.isInteger(y) ==> foo(x, y) !== 0 }`
(`tests/fixtures/e2e/readme-example.ts:2`):

```lean
theorem foo.nonzero : ∀ (x : Int) (y : Float),
    y.isInteger = true → ((foo x y != 0.0) = true) := by
  thales_auto   -- the "single curated tactic" of docs/future.md:89-90
```

The statement piece is mechanical once the emitter can produce a `theorem`
declaration; the *proof* piece is the future.md automation story and out of
scope for this analysis.

## 2. `prefix ::= FORALL binder-group+` — translatable today

**Pabst.** `src/prefix-parser.ts:24-35`: `∃`/`exists` is rejected with a
teaching error (PBT cannot soundly confirm ∃); a quantifier token *inside*
the body is rejected as a nested quantifier (`src/formula-lexer.ts:159-166`).
So the only prefix Thales will ever see is a single leading `∀`.

**Thales/Lean.** Lean's `∀` is the native counterpart; nothing to widen.
The two pabst rejections are load-bearing for Thales too: no ∃ means no
choice between `∃` (undecidable to test) and `Σ`-types, and no nested
quantifiers means the formula body stays quantifier-free — every atom is a
closed boolean expression over the binders, exactly the shape Thales's
expression lowering handles.

## 3. `binder-group ::= "(" var-name+ ":" domain constraint? ")"` — translatable today

**Pabst.** `src/prefix-parser.ts:191-246` (`parseBinderGroup`); grouping is
explicitly Lean-style — `(x y: int)` binds both with the same domain
(`docs/grammar.ebnf:31-33`). `var-name` is `/^[A-Za-z_][A-Za-z0-9_]*$/`
(`src/prefix-parser.ts:18`).

**Thales/Lean.** `(x y : Int)` is verbatim Lean binder syntax. Every pabst
var-name is a lexically valid Lean identifier; the only hazard is collision
with Lean keywords (`theorem`, `def`, …), which the emitter already tracks —
`Thales/Emit/LeanSyntax.lean:276` carries the reserved list used for
renaming. Direct reuse.

## 4. The six binder domains — mixed

Pabst's domain table (`src/domains.ts:5-12`):

| domain | fast-check arbitrary | generated TS type | Thales/Lean image | evidence |
|--------|---------------------|-------------------|-------------------|----------|
| `int` | `fc.integer()` | `number` (safe-integer valued) | prelude `Integer` | below |
| `nat` | `fc.nat()` | `number` (0…2^53−1) | prelude `Natural` | below |
| `number` | `fc.double()` | `number` | `Float` | `Thales/Emit/Lean.lean:97`, `docs/subset.md:65` |
| `boolean` | `fc.boolean()` | `boolean` | `Bool` | `Thales/Emit/Lean.lean:100` |
| `string` | `fc.string()` | `string` | `String` | `Thales/Emit/Lean.lean:99` |
| `bigint` | `fc.bigInt()` | `bigint` | `Int` | `Thales/Emit/Lean.lean:98` |

### 4a/4b. `int` and `nat` — translatable today, via the prelude subtypes

`nat` has no TS counterpart and `int` is not a TS type either: both generate
JS `number` values (fc.integer/fc.nat return doubles), and pabst clamps both
to the safe-integer range `±9007199254740991` (`src/domains.ts:18,34-49`:
`intBounds` intersects with `MAX_SAFE`; `nat` floors at 0).

Thales already has *exactly* these sets as first-class types:
`@thales/prelude`'s `Integer` and `Natural`, lowered as Lean subtypes of
`Float` (`docs/subset.md:1055-1066,1140-1141`):

```lean
Integer := {x : Float // x.isInteger && x.abs ≤ 2^53 - 1}
Natural := {x : Float // x.isInteger && 0 ≤ x && x ≤ 2^53 - 1}
```

So the faithful lowering is `∀ (x : Integer), …` / `∀ (n : Natural), …`, with
island occurrences of the binder projected via `.val` — the emitter already
does that projection for arithmetic and comparisons on refinement operands
(`Thales/Emit/Lean.lean:548-552,583-587`).

**Deliberately not Lean `Nat`/`Int`.** Idealizing `int` → `Int` reads nicer
and proves easier, but is unfaithful: island arithmetic runs in doubles, so
`x * x` for `x` near 2^53 rounds in JS while `Int` multiplication doesn't.
The Float-subtype image keeps the theorem about the program that actually
runs. An opt-in idealized mode (`int` → `Int` plus a side condition that the
island stays within safe range) is a possible future design, but the default
should be the faithful one. Note `Nat` appears nowhere in Thales's user
surface today — it is runtime-internal only (`Thales/TS/Runtime.lean:303,425,631`).

### 4c. `number` — thorny, needs decision (the biggest thorn)

Pabst `number` is honest IEEE: `fc.double()` including ±Infinity (NaN only
excluded when an interval guard is present — `src/domains.ts:131-141` adds
`noNaN: true` for *guarded* binders; an unguarded `(x: number)` does
generate NaN).

Thales lowers `number` → Lean `Float` throughout (`Thales/Emit/Lean.lean:97`,
`docs/subset.md:65`), and the runtime models NaN/Infinity as `0.0/0.0`,
`1.0/0.0` (`Thales/TS/Runtime.lean:403,406`). **Executing** a property body
in Lean is therefore fine — the conformance harness already byte-matches
Float programs. **Proving** is the problem: Lean 4 core's `Float` operations
are opaque/`@[extern]` with no axiomatized IEEE theory; there are no usable
lemmas about `Float` `+`/`*`/`<` in core or Batteries (Thales depends only on
Batteries and lean-regex, `lakefile.lean:10-11`). A theorem
`∀ (y : Float), …` is *stateable* today but provable only by `native_decide`
-style evaluation on closed instances — which a `∀` over `Float` never is.

Options for the design decision (issue #96's first known thorn):

1. **Reject `number` binders in v1** of the translation; accept `int`, `nat`,
   `bigint`, `boolean`, `string`. Cheapest, honest, and mirrors how Thales
   entered other features (subset-first). Pabst still tests `number`
   properties; they just don't escalate to Lean yet.
2. **Idealize** `number` → `ℝ` or `ℚ`: unsound (float associativity fails —
   pabst even ships a fixture demonstrating it,
   `tests/fixtures/e2e/float-associativity.ts`) and would need Mathlib.
3. **State over `Float`, prove nothing yet**: emit the theorem with the
   curated tactic and let it fail gracefully into "tested but not proved".
   Compatible with future.md's dual-discharge framing (`docs/future.md:85-92`).

Recommendation: 1 now, 3 as the follow-on; never 2 silently.

### 4d. `boolean` — translatable today

`fc.boolean()` ↔ TS `boolean` ↔ Lean `Bool`
(`Thales/Emit/Lean.lean:100`). Total, decidable, no caveats.

### 4e. `string` — translatable today (encoding caveat)

`fc.string()` ↔ TS `string` ↔ Lean `String`
(`Thales/Emit/Lean.lean:99`). Two documented caveats carry over unchanged
from the compiler: JS strings are UTF-16 code-unit sequences, Lean `String`
is Unicode scalars, so `.length` diverges on non-BMP content
(`docs/subset.md:1028-1038`), and only `length`/`startsWith`/`endsWith`/
`split` are lowerable string methods (TH0087, `docs/errors.md:987-1010`) —
islands using other methods are gated (see §11). Additionally, fast-check
can generate strings a `String`-of-scalars model cannot represent exactly
(lone surrogates); a property whose counterexample is a lone-surrogate
string has no Lean image. Worth a one-line documented divergence, same
posture as `docs/subset.md`'s existing string section.

### 4f. `bigint` — translatable today (termination caveat)

`fc.bigInt()` ↔ TS `bigint` ↔ Lean `Int` (`Thales/Emit/Lean.lean:98`,
`docs/subset.md:65`). Exact-integer semantics match. One inherited caveat:
if the *island* calls a recursive function on `bigint`, `Int` recursion has
no structural decrease — `@total` on `fact(n - 1n)` is rejected today and
automatic `termination_by` emission is deferred (`docs/subset.md:886-891`,
`docs/errors.md:593-606`). That's a property-of-the-callee issue, not of the
binder, but it bounds which `bigint` properties can be *proved* rather than
stated.

## 5. `constraint ::= MEMBER guard` — needs subset widening

**Pabst.** `src/prefix-parser.ts:216-229`: after `∈`/`in`, a leading `/`
routes to `parseRegexGuard`, anything else to `parseRange`. Guards are
per-domain exclusive: intervals on numeric domains only, regex on string
only (`src/range.ts:23-28`, `src/regex-guard.ts:79-82`).

**Thales.** Nothing corresponds today — but the machinery it needs is the
already-specced refinement-types layer: `docs/future.md:76-83` (user-defined
`@refine` → Lean subtype) and `docs/specs/basic-refinement-types.md`. A
binder constraint is precisely a refinement on the binder's type.

**Lowering sketch** — two equivalent shapes, pick per proof ergonomics:

```lean
-- hypothesis style (recommended: friendlier to automation)
theorem f.p : ∀ (x : Int), 1 ≤ x → x ≤ 30 → ⟦body⟧ = true
-- subtype style (matches the prelude's existing pattern, docs/subset.md:1140)
theorem f.p : ∀ (x : {n : Int // 1 ≤ n ∧ n ≤ 30}), ⟦body⟧ = true
```

## 6. `regex-literal` guard — thorny, needs decision

**Pabst.** `src/regex-guard.ts:79-121` (`parseRegexGuard`): whole-string
semantics via auto-anchoring `^(?:…)$` (`anchoredSource`, :63-65); flags
restricted to `s`/`u` (:101-105); the pattern must be one fast-check's
`stringMatching` supports, *probed at parse time against the same fast-check
copy the spec will run* (:113-119) so the accepted subset cannot drift.
Lowered as `fc.stringMatching(/^(?:src)$/flags)` (`src/domains.ts:113-122`).

**Thales.** Regex literals are rejected outright in program code: TH0091,
`Thales/Emit/SubsetCheck.lean:359`
(`| .literal base (.regex _ _) _ => #[mkThalesDiag .regexLiteral base.loc]`),
documented at `docs/errors.md:1084-1092` — "Thales has no Lean lowering for
`RegExp` values". Two important nuances:

1. **TH0091 does not directly block this production.** A pabst regex guard
   lives in the JSDoc annotation, not in a program expression, so the
   subset check never sees it. The gap is denotational: Thales has no Lean
   meaning for "string matching pattern p", which is also exactly why
   TH0091 exists.
2. **The Lean ingredient is already pinned:** `lakefile.lean:11` requires
   `pandaman64/lean-regex` (staged for issue #83), though no module imports
   it yet (grep: no `import Regex` under `Thales/` or `Test/`).

**Lowering sketch** (once lean-regex is wired in):

```lean
theorem f.p : ∀ (s : String), (re"^(?:[a-z]+)$").isMatch s = true → ⟦body⟧ = true
```

**Why it stays thorny:** three regex dialects must agree — (a) JS `RegExp`
with `u` semantics (the guard's meaning at pabst runtime), (b) fast-check's
`stringMatching`-supported subset (already the accepted-at-parse-time gate),
and (c) lean-regex's supported syntax/semantics. The design decision is
which intersection Thales accepts and whether matching is asserted to be
*equivalent* or merely both-anchored-PCRE-ish. Pabst's parse-time probing
pattern (validate against the engine you'll actually run) is the right model
to copy: Thales should validate guards against lean-regex's parser at
compile time and reject patterns outside the intersection, mirroring how
TH0091 keeps the current subset honest.

## 7. `interval`, `endpoint`, `INFINITE` — needs subset widening (number corners thorny)

**Pabst.** `src/range.ts:22-66` parses `[`/`(` … `]`/`)` with legally
mismatched delimiters; endpoint literal syntax is per-domain
(`src/range.ts:7-9,154-179`); ∞ endpoints must be exclusive for
int/nat/bigint (:88-94). Lowering (`src/domains.ts:34-104`):

- **int/nat**: open endpoints fold into ±1, nat floors at 0, everything is
  intersected with the safe-integer range (with a clamping warning,
  `src/range.ts:119-124`); result is inclusive `fc.integer({min, max})`.
- **bigint**: same ±1 folding, unbounded sides stay unbounded.
- **number**: exact `fc.double` constraints with `minExcluded`/`maxExcluded`
  and `noNaN: true`; emptiness is judged in fast-check's own double ordering,
  where **every double is distinct: −0 sits below 0** (so `[0, -0]` is empty
  but `(-0, 0]` is `{0}`), and an excluded bound removes exactly one double
  by adjacency (so `[-1, 0)` can generate −0, and `(0, 5e-324)` is empty)
  (`src/range.ts:127-152`).

**Thales.** No interval machinery, but the target shape exists: the prelude
types are literally interval subtypes of `Float`
(`docs/subset.md:1140-1141`), and comparison operators lower cleanly for
`Float`, `Int` (`Thales/Emit/Lean.lean:306-309`).

**Lowering sketch.** For int/nat/bigint the clean move is to lower the
*folded, clamped* bounds pabst itself computes — closed integer bounds, so
open/closed distinctions and ∞ endpoints vanish on the Lean side:
`∀ (x : Integer), (1 : Float) ≤ x.val → x.val ≤ 30 → …` (or `Int` bounds for
bigint). This has a semantic footnote worth a documented decision: for
clamped intervals the theorem then quantifies over the *tested* set (the
clamp), not the written set — arguably correct (matches what pabst verified)
but it should be explicit. For `number`, hypothesis lowering `lo < x → x ≤ hi`
in `Float` ordering does **not** match fast-check's ordering at the −0/0
boundary (Lean `Float` `<` is IEEE, where `-0 < 0` is false); intervals with
−0 endpoints or exclusive finite endpoints near it inherit the §4c decision.
Practical posture: support number intervals with the ordinary IEEE reading,
document the −0-endpoint corner as out of scope (or reject −0 endpoints),
and fold the rest into the `number` decision.

## 8. Formula connectives (`formula`…`primary`, :69–91) — translatable today

**Pabst.** Recursive-descent chain in `src/formula-parser.ts:39-122`
(precedence ↔ < → < ∨ < ∧ < ¬; ↔ non-associative :44-49; ∧/∨
left-associative; `primary` distinguishes logical grouping from island
parens by the wholly-wrapped test :97-122). Executable lowering is Bool-
valued JS (`src/lower.ts:5-29`): `¬`→`!`, `∧`→`&&`, `∨`→`||`,
`↔`→`===` on booleans, nested `→`→`(!p || q)`.

**Thales.** All the Bool ingredients exist and are TH0026-guarded to
*genuine* booleans: `&&`/`||`/`not` lower directly
(`Thales/Emit/Lean.lean:776-788`), `===` on `Bool` is `==`
(`Thales/Emit/Lean.lean:303-305`), and non-boolean operands are rejected
statically (`docs/errors.md:366-399`).

**Lowering sketch — the Bool-image choice.** Two candidate images:

1. **Bool image (recommended):** translate the whole formula exactly as
   `lowerExpr` does — one `Bool` expression using `!`, `&&`, `||`, `==`,
   `!p || q` — and state `⟦formula⟧ = true`. This is definitionally the
   same expression pabst executes, so tested and proved artifacts agree
   token-for-token; `decide`/`simp` handle the propositional skeleton.
2. **Prop image:** `∧`/`∨`/`¬`/`→`/`↔` as Prop connectives over
   `atom = true` leaves. Prettier for humans, but introduces a
   translation-of-the-translation (Bool/Prop coercion points) that has to
   be proven equivalent to what fast-check ran.

Either way this production is ready; the choice is ergonomic, not semantic
(`Bool` and decidable-`Prop` images are interconvertible by `decide`).

## 9. Root implication as precondition (`fc.pre`) — translatable today

**Pabst.** The one place operational and logical semantics diverge in the
grammar: at the formula root, `a → b → c` makes `a`, `b` *sample discards*
— `src/lower.ts:36-47` (`lowerTop`) lifts antecedents to
`fc.pre(a); fc.pre(b);` (`src/emit.ts:96`), while a *parenthesized* `→` is
material `(!p || q)` (`src/lower.ts:22-29`). Discarding too much surfaces as
an `exhausted` issue (`src/runtime.ts:70-76`,
`tests/fixtures/e2e/precondition-exhausted.ts`).

**Thales/Lean.** This distinction **vanishes in a theorem statement** — the
happiest finding of the analysis. `fc.pre(P); assert Q` tests exactly the
samples where `P` holds, i.e. establishes evidence for `∀ x, P x → Q x`; a
material `(!P || Q)` body asserts the same proposition. In Lean both lower
to the same `→`:

```lean
theorem foo.nonzero : ∀ (x : Int) (y : Float),
    ⟦Number.isInteger(y)⟧ = true → ⟦foo(x, y) !== 0⟧ = true
```

The natural convention: root antecedents become named hypotheses (nice for
tactics and for error messages), nested `→` stays inside the Bool image as
`!p || q` (or `→` in the Prop image). No decision needed; fc.pre's
discard-vs-vacuous distinction is purely about sampling efficiency, which
has no Lean counterpart.

## 10. `atom`, `EQUATION` ≡/≢ = `Object.is` — thorny for `number`, translatable otherwise

**Pabst.** `src/equations.ts:17-172` (`desugarEquations`): a depth-0 `A ≡ B`
becomes `Object.is(A, B)`, `A ≢ B` becomes `!Object.is(A, B)` (:119-132);
chained equations rejected (:94-99); nested glyphs rejected with a
call-Object.is-directly hint (:152-159); `≠` rejected with a write-≢ hint
(:25-29).

**Thales.** `Object.is` appears nowhere in `Thales/` (grep). Equality lowers
to Lean `==` (`BEq`): `Thales/Emit/Lean.lean:301-305` maps both `==` and
`===` to Lean `==`. For `Float` that is IEEE equality — the runtime is
explicit that this *matches JS strict equality*: "Lean `Float` `BEq` is IEEE
(`NaN ≠ NaN`, `+0 = -0`)" (`Thales/TS/Runtime.lean:456-457`; NaN divergence
note `docs/subset.md:1041-1043`). `Object.is` is SameValue, which differs
from `===`/IEEE `==` in exactly two places: `Object.is(NaN, NaN) = true` and
`Object.is(0, -0) = false`.

**Per-domain resolution:**

- `bigint` → `Int`, `string` → `String`, `boolean` → `Bool`, `int`/`nat` →
  prelude subtypes with integer-valued `Float`s excluding NaN/−0 by the
  refinement: on all of these, `Object.is` coincides with `===`, which
  coincides with Lean `==`/`=`. **Translatable today** — ≡ lowers to the
  existing equality.
- `number` → `Float`: needs a new runtime definition with SameValue
  semantics, e.g.

  ```lean
  def sameValue (a b : Float) : Bool :=
    if a.isNaN || b.isNaN then a.isNaN && b.isNaN
    else a.toBits == b.toBits          -- distinguishes +0/-0, else IEEE-equal values share bits
  ```

  Definable in core Lean (`Float.toBits` exists), and *executing* it is
  fine. But **proving** anything through `toBits` hits the same opaque-
  `Float` wall as §4c, and it also touches the "don't widen the runtime"
  convention (CLAUDE.md): a runtime helper lands only alongside an emitter
  change. So ≡ on `number` inherits the §4c decision — under option 1
  (reject `number` binders initially), ≡/≢ is translatable for everything
  that remains, and `sameValue` lands when `number` does.

## 11. `island` — needs subset widening, per island; the gate already exists

**Pabst.** An island is an opaque TS expression (`docs/grammar.ebnf:103-106`)
— `as`, `satisfies`, generic call arguments, non-null `!` are explicitly
island language. Every free identifier must be exported from the annotated
module (`src/free-idents.ts:55-73`), with a whitelist of JS globals
(`src/free-idents.ts:4-27`: `Math`, `Number`, `JSON`, `Object`, `Date`,
`Map`, `Set`, `RegExp`, `console`, …).

**Thales.** This is where the two tools meet mid-pipeline: an island is just
a TS expression, and Thales already has a full expression subset with a
diagnostic gate. Much of what islands realistically contain is **in-subset
today**: arithmetic and comparisons (`Thales/Emit/Lean.lean:306-309`),
ternary `?:` (`:794-795`), `??` → `Option.getD` (`:781-782`), optional
chaining (`Thales/Emit/SubsetCheck.lean:306-307` recurses without
diagnostic), template literals (`Thales/Emit/Lean.lean:998-1016`), arrow
callbacks (`:962-996`), `.map`/`.filter`/`.reduce`
(`Thales/TS/Runtime.lean:626-637`), `Number.isNaN` (`:588-589`,
`Thales/Emit/Lean.lean:915-916`), calls to exported module functions
(TH0088–90 module machinery, `docs/errors.md:1012-1082` — which dovetails
with pabst's exported-identifier rule). Out-of-subset islands are *already
rejected by name*: regex values TH0091 (`Thales/Emit/SubsetCheck.lean:359`),
`typeof`/`void`/`delete` TH0092 (`:261-268`), unlowerable array-method
receivers TH0085, unsupported string methods TH0087, mutating methods
TH0004 (`docs/errors.md:45-96`). Most of pabst's `GLOBALS` (`Math`, `JSON`,
`Date`, `Map`, `Set`, `console`) have no Thales lowering yet.

**Consequence.** The island production needs no new *design* — the existing
accept-or-TH-reject pipeline is precisely the right gate. The work is the
ordinary, incremental subset widening already underway (each missing global
or method is its own slice, in the style of #83/#85). A pabst annotation
whose islands type-check under Thales's subset is translatable end-to-end;
one that doesn't gets a precise TH diagnostic naming the offending
construct, which is exactly the right UX for "this property can be tested
but not yet proved".

## 12. Atom side conditions / island hygiene — translatable today (Thales is stronger)

Pabst enforces five hygiene rules; each has a Thales counterpart that is
static rather than dynamic:

| Pabst rule (evidence) | Pabst enforcement | Thales counterpart |
|---|---|---|
| Atoms must be genuine booleans (`src/runtime.ts:38-51`, `bool()`) | **runtime** throw per atom | **static**: TH0026 boolean-condition typing (`docs/errors.md:366-399`); a non-boolean atom fails type-check before emission |
| No JS `&&`/`\|\|`/`!` at atom top level (`src/equations.ts:295-318`) | parse-time | syntax-level concern with no Lean impact; leaf-level `&&`/`\|\|` lower to Bool ops (`Thales/Emit/Lean.lean:776-788`) |
| Loose `==`/`!=` banned (`src/equations.ts:102-115`) | parse-time | moot for lowering — Thales maps `.eq` to Lean `==` anyway with a "loose; for now" comment (`Thales/Emit/Lean.lean:301-302`); pabst's ban conveniently keeps that soft spot unexercised |
| Assignments banned anywhere in an atom (`src/equations.ts:272-291`) | parse-time (TS AST walk) | static purity: TH0001–TH0007 mutation family (`docs/errors.md:47-53`) |
| Free identifiers must be exported (`src/free-idents.ts:55-73`) | parse-time | named-export module subset TH0088–TH0090 (`docs/errors.md:1012-1082`) |

The one behavioral note: pabst's `__bool` check exists because generated JS
can't see types; Thales *can*, so on the Lean side the check dissolves into
typing — a proved property never needs the runtime guard. No gap.

---

## Recommended design decisions (the thorny residue)

1. **`number` binders (§4c)** — the load-bearing decision. Recommended: v1
   rejects `number` binders for Lean escalation (pabst still tests them);
   follow-on states `Float` theorems that route to "tested, not proved"
   under the dual-discharge framing of `docs/future.md:85-92`. Do not
   idealize to `ℝ`/`ℚ` silently (pabst's own
   `tests/fixtures/e2e/float-associativity.ts` is the counterexample).
2. **Regex guards (§6)** — wire in the already-pinned `lean-regex`
   (`lakefile.lean:11`) and accept only the intersection of the JS-`u`,
   fast-check-`stringMatching`, and lean-regex dialects, validated at
   compile time in the same probe-the-real-engine style as
   `src/regex-guard.ts:113-119`. Ties into existing issue #83.
3. **≡/≢ on `number` (§10)** — blocked on (1); when `number` lands, add a
   `sameValue : Float → Float → Bool` runtime def (NaN-reflexive,
   −0-distinguishing via `Float.toBits`); on every other domain ≡ is the
   existing Lean equality today.
4. **Clamped/number intervals (§7)** — decide whether interval theorems
   quantify over the written set or the tested (clamped, fc-ordered) set;
   recommended: the tested set, documented, with −0 endpoints on `number`
   intervals rejected or documented out of scope.
5. **Bool vs Prop formula image (§8)** — recommended: Bool image with a
   single `= true` at the root, so the proved expression is
   token-identical to what fast-check executed; root antecedents (§9)
   become hypotheses.

## Headline

Nothing in the grammar's *logical* skeleton is hard: quantifier prefix,
Lean-style binder groups, the full connective chain, precondition-vs-
material implication, and all the hygiene rules map onto Lean and onto
Thales's existing static checks essentially for free — with fc.pre-vs-→
collapsing entirely. The genuine gaps are concentrated where JS numerics
meet Lean's opaque `Float` (`number` binders, `Object.is` equations, −0
interval corners — one decision, really) plus one dialect-intersection
problem (regex guards) for which the Lean-side dependency is already
pinned. Four of the six binder domains are translatable today, two of them
because the `@thales/prelude` `Integer`/`Natural` subtypes turn out to be
exactly fast-check's `fc.integer()`/`fc.nat()` value sets.
