# Thales-TS Examples

Each `.ts` file in this directory is one example program. The harness
(`scripts/run-examples.js`) runs each through the conformance contract.

Examples fall into two categories, distinguished by whether the file
contains a `// @thales-expect-error` directive.

## Accepting examples

Both `tsc` and `thales` accept the file; the runtime byte-match stage is
performed.

Per stage:

1. **Type-check agreement.** `tsc --strict` (via `tsconfig.json` +
   `--ignoreConfig`) and `thales --no-emit` are run over the file; every
   `TSXXXX` diagnostic tsc produces at line L must also appear in thales's
   output at line L. thales may additionally report `TH####` diagnostics
   for subset violations.
2. **Runtime agreement** (only if both type-checkers accept the file).
   `tsx file.ts` and `thales file.ts && lake env lean <File>.lean` must
   produce identical stdout, stderr, and exit code.

An accepting example passes if both stages agree. A
`// @thales-skip-runtime …` line comment disables the runtime stage
(currently only `utf16-string-length.ts`, where JS's UTF-16 `.length`
diverges from Lean's Unicode-scalar count).

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
npm install                 # pinned tsc + tsx
node scripts/run-examples.js
```

## Adding an example

Create a new `.ts` file in this directory with a descriptive name. That's
it — no frozen `expected.*` files, no extra artifacts. On next run, the
harness will verify the file against `tsc`, `tsx`, and the Lean emission
path.

For a subset-rejected example, prefix the name with the four-digit TH
code and add a `@thales-expect-error` directive above each line that thales
flags. See `docs/subset.md` for the grammar.
