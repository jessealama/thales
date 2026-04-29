# Thales-TS Examples

Each `.ts` file in this directory is one example program. They serve as bth tests and documentation. We have a harness, `scripts/run-examples.js`, that runs each through the conformance contract, described below, which is:

Both `tsc` and `thales` accept the file, as well as:

1. **Type-check agreement.** `tsc --strict` (via `tsconfig.json` +
   `--ignoreConfig`) and `thales --no-emit` are run over the file; every
   `TSXXXX` diagnostic tsc produces at line L must also appear in thales's
   output at line L. thales may additionally report `TH####` diagnostics
   for subset violations.
2. **Runtime agreement** (only if both type-checkers accept the file).
   `tsx file.ts` and `thales file.ts && lake env lean <File>.lean` must
   produce identical stdout, stderr, and exit code.

An accepting example passes if both stages agree.

## Subset-rejected examples

`tsc` accepts; `thales` rejects with one or more `TH####` codes, each
documented by a `@thales-expect-error` directive above the violating line.
These document the current boundaries of Thales-TS vs. plain
TypeScript. The runtime stage is skipped (the file cannot be emitted to
Lean). Files are named `<NNNN>-<slug>.ts`, where `NNNN` is the TH code
(e.g. `0030-class.ts` demonstrates TH0030).

See `docs/subset.md` for the directive semantics and `docs/errors.md`
for the TH-code catalogue.

## Running

```bash
lake build thales           # emit + type-check binary
npm install                 # installs tsc and tsx
node scripts/run-examples.js
```

## Adding an example

Create a new `.ts` file in this directory with a descriptive
name. On next run, the harness will verify the file against
`tsc`, `tsx`, and the Lean emission path.

For a subset-rejected example, prefix the name with the
four-digit TH code and add a `@thales-expect-error`
directive above each line that thales flags. See
`docs/subset.md` for the grammar.
