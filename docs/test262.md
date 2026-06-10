# test262

Thales runs a sliced subset of [tc39/test262](https://github.com/tc39/test262)
as a progress metric for subset widening (issues #23–#29). Each test is
classified as **skipped**, **out-of-subset**, **pass**, or **fail**, where
_pass_ means thales compiles the test and the emitted Lean's runtime
behavior is byte-identical (stdout, stderr, exit code) to Node's — the same
bar as the conformance corpus (`scripts/run-examples.js`).

## Philosophy

- **Verbatim tests.** Test bodies run exactly as shipped; nothing is
  rewritten. A test that doesn't compile classifies honestly as
  out-of-subset. As the subset widens, the runner is a target we grow into.
- **Authored shim, no concessions.** test262's two implicit harness files
  (`sta.js`, `assert.js`) are untyped sloppy JS; `tests/test262/harness/`
  holds hand-written strict-TS ports with the same observable behavior.
  The shim is plain strict TS with no concessions to today's subset —
  compiling it is itself a tracked target. Diagnostics are attributed
  `shim` vs `body` so "blocked only by the shim" is visible.
- **Honest denominators.** Tests unevaluable under the scheme (negative,
  noStrict, module, async, raw, unported includes) are skipped with
  per-reason counts. The pass-rate denominator is runnable tests only:
  pass ÷ (pass + fail).

## Running locally

    npm run setup:test262                          # one-time: submodule + sparse-checkout
    node scripts/run-test262.js                    # all slices (human table)
    node scripts/run-test262.js --dir do-while     # one slice
    node scripts/run-test262.js --json             # machine-readable report

The slice list lives in `scripts/test262-slices.json`; after editing it,
re-run `npm run setup:test262`. CI runs the full slice set in the monthly
conformance workflow (`conformance-monthly.yml`, also dispatchable
on demand).

## Classification

1. Frontmatter skip buckets (checked in order): `negative`, `noStrict`,
   `module`, `async`, `raw`, `include:<name>`. `*_FIXTURE.js` files are
   not tests and are not enumerated.
2. A composite file — `"use strict";` + shim + verbatim body — is checked
   with `thales --no-emit`. Any diagnostic ⇒ **out-of-subset** (codes
   recorded, attributed shim/body). tsc is not run; thales alone decides.
3. If clean: `tsx` vs thales-emit + `lake env lean`, byte-compared.
   Identical ⇒ **pass**; emit/elaboration failure ⇒ **fail (compile)**;
   byte mismatch ⇒ **fail (runtime)**; timeout either side ⇒
   **fail (timeout)**.

## Baseline

thales `98610ec`, test262 `fc32f3e8`, 2026-06-10:

```
Slice                                             Total  Skip   OoS  Pass  Fail  InSubset   Pass%
-------------------------------------------------------------------------------------------------
test/language/expressions/postfix-increment          38    18    20     0     0         0     n/a
test/language/expressions/prefix-increment           33    13    20     0     0         0     n/a
test/language/expressions/compound-assignment       454   100   354     0     0         0     n/a
test/language/statements/for-of                     751   174   577     0     0         0     n/a
test/language/statements/for                        385    72   313     0     0         0     n/a
test/language/statements/while                       38    19    19     0     0         0     n/a
test/language/statements/do-while                    36    18    18     0     0         0     n/a
TOTAL                                              1735   414  1321     0     0         0     n/a

Skip reasons (all slices):
  negative: 227
  noStrict: 121
  include:propertyHelper.js: 43
  include:compareArray.js: 7
  include:tcoHelper.js: 6
  include:compareArray.js,resizableArrayBufferUtils.js: 5
  include:compareArray.js,propertyHelper.js: 3
  async: 1
  module: 1

Top blocking diagnostics (tests blocked, by attribution):
Code              Shim   Body  Unknown
TS2339            1179    895        0
TH0001            1179    451        0
TS2304            1179     77        0
TH0030            1179     48        0
TH0063            1179      2        0
TH0021            1179      0        0
TH0031            1179      0        0
TH0060            1179      0        0
TS2349            1179      0        0
TH0010               0    765        0
TH0002               0    150        0
parse-error          0      0      142
TH0003               0     36        0
TS2364               0     12        0
TH0004               0      5        0
```

Reading the baseline: every runnable test is blocked at minimum by the
shim (1,179 tests; classes/namespaces — TH0030/TH0031 et al., plus the
spurious TS2304s of #31). The dominant body blockers are loops (TH0010,
765 tests) and mutation (TH0001, 451) — precisely the #24–#26 widening
targets. `parse-error` counts tests where thales hard-fails without a
structured diagnostic (e.g. multi-declarator `var x, y;`).

This table is updated manually when a feature lands; the per-directory
numbers are the metric quoted in #24–#29.
