# Thales-TS Conformance Corpus

Each `.ts` file under this directory is one conformance test. They serve as both tests and documentation. The harness `scripts/run-examples.js` runs each file through the conformance contract described below.

## Layout

```
tests/conformance/
├── accept/   tsc and thales both accept; runtime output matches byte-for-byte
├── mirror/   tsc and thales both reject; TS codes and lines match (no runtime stage)
├── reject/   tsc accepts; thales rejects with TH#### (no runtime stage)
├── throws/   both type-check; both runtimes must throw (throw-iff equivalence)
└── future/   parked: design intent only, not visited by the harness
```

Directory membership _is_ the test specification — the harness routes each file according to its bucket. No additional directives mark the expected outcome.

## The contract

1. **Type-check agreement.** `tsc --strict` (via `tsconfig.json` +
   `--ignoreConfig`) and `thales --no-emit` are run over the file; every
   `TSXXXX` diagnostic tsc produces at line L must also appear in thales's
   output at line L. thales may additionally report `TH####` diagnostics
   for subset violations.
2. **Runtime agreement** (only if both type-checkers accept the file).
   `tsx file.ts` and `thales file.ts && lake env lean <File>.lean` must
   produce identical stdout, stderr, and exit code. For files under
   `throws/`, the relaxed throw-iff rule applies: both runtimes must
   throw (messages and exit codes may differ).

## Buckets

### `accept/`

Both `tsc` and `thales` accept the file; both runtimes produce byte-identical output.

### `mirror/`

`tsc --strict` and `thales --no-emit` must both reject the file with the same `TSXXXX` codes at the same lines. No `@thales-expect-error` directives (these are mirror-of-tsc errors, not subset violations). The runtime stage is skipped — files do not emit. Used for the read-only / non-lvalue family (TS2540, TS2588, TS2364) and other tsc-error mirrors. Filename convention: descriptive slug; no TH prefix.

### `reject/`

`tsc` accepts; `thales` rejects with one or more `TH####` codes, each documented by a `@thales-expect-error` directive above the violating line. The runtime stage is skipped (the file cannot be emitted to Lean). Files demonstrating a single TH code are named `<NNNN>-<slug>.ts` (e.g. `0030-class.ts` demonstrates TH0030).

### `throws/`

Both type-checkers accept the file; the program throws at runtime. The harness asserts the _relaxed_ throw-iff equivalence — both `tsx` and the Lean emission must throw, but their messages and exit codes need not match. Filename convention: `<feature>-throw.ts`.

### `future/`

Parked fixtures: valid against the intended Thales subset, but the current compiler can't fully check or emit them. The harness skips this directory. See `tests/conformance/future/README.md`.

See `docs/subset.md` for the directive semantics and `docs/errors.md` for the TH-code catalogue.

## Running

```bash
lake build thales           # emit + type-check binary
npm install                 # installs tsc and tsx
npm run conformance         # full corpus
npm run conformance:self-test   # harness regression suite
```

## Adding a test

Create a `.ts` file in the appropriate bucket:

- **`accept/`** — pick a descriptive slug; nothing extra to do.
- **`reject/`** — prefix the filename with the four-digit TH code if the test targets a single code (`<NNNN>-<slug>.ts`), and add a `@thales-expect-error` directive above each line that thales flags. See `docs/subset.md` for the grammar.
- **`throws/`** — name the file `<feature>-throw.ts`; it should import from `@thales/prelude` (or otherwise produce a runtime throw that the Lean emission mirrors).
