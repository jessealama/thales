#!/usr/bin/env node
// scripts/run-examples.js
// Drives the Thales-TS ↔ TypeScript conformance harness.
//
// Environment assumptions (CI pins these; local runs may differ):
//   NODE_VERSION 24.x, LC_ALL=C.UTF-8, TZ=UTC, lean-toolchain from repo.

import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {
  repoRoot,
  thalesBin,
  parseDiagnostics,
  fmtDiag,
  diagnoseAgreement,
  runCapture,
  runTsx,
  runThcThenLean,
  diffRuns,
  preflight,
} from './lib/harness.js';

const conformanceDir = path.join(repoRoot, 'tests', 'conformance');
const fixturesDir = path.join(repoRoot, 'Test', 'Examples', 'fixtures');

// ---- pure helpers ----

/** Regex test for directive presence in a TS source string. Naive: may
 *  over-match inside string/template literals, which is fine — thales is the
 *  source of truth for correctness, and the harness only needs to pick the
 *  flow. The pattern mirrors the Lean `isLooseMatch` so near-miss typos
 *  (e.g. `@thales-expect-erorr`, `@thales_expect_error`) route through the
 *  directive flow and surface TH9003 from thales. */
function hasDirectivePure(src) {
  return /^[ \t]*\/\/[ \t]*@thales[-_]?expect[-_]?e/m.test(src);
}

/** Does input.ts contain (at least loose) `@thales-expect-error`? */
function hasDirective(inputPath) {
  return hasDirectivePure(fs.readFileSync(inputPath, 'utf8'));
}

/**
 * Does input.ts import from `@thales/prelude`? Used to gate the relaxed
 * throw-iff equivalence rule: when prelude is in use, throwing constructors
 * (`asInteger`, `asNatural`, etc.) may throw at runtime even though the
 * program is well-typed. In that case we require only throw-iff equivalence
 * (both sides exit nonzero), not byte-identity of stdout/stderr/exit.
 *
 * Detection is a regex scan of the source text; it may over-match in
 * string literals but that is harmless (only widens the relaxation).
 */
function importsPrelude(inputPath) {
  const src = fs.readFileSync(inputPath, 'utf8');
  return /\bfrom\s+["']@thales\/prelude["']/.test(src);
}

/** Parse input.ts and build a map from appliesToLine (1-based) to the set
 *  of codes declared for that line (null for the code-less form). */
function collectDeclaredDirectives(inputPath) {
  const lines = fs.readFileSync(inputPath, 'utf8').split(/\r?\n/);
  const re = /^[ \t]*\/\/[ \t]*@thales-expect-error(?:[ \t]+TH(\d{4}))?[ \t]*$/;
  const declared = new Map();
  for (let i = 0; i < lines.length; i++) {
    const m = lines[i].match(re);
    if (!m) continue;
    let j = i + 1;
    while (j < lines.length) {
      const trimmed = lines[j].replace(/^[ \t]+/, '');
      if (trimmed === '' || /^\/\//.test(trimmed)) {
        j++;
        continue;
      }
      break;
    }
    const appliesToLine = j < lines.length ? j + 1 : 0;
    const code = m[1] ? Number(m[1]) : null;
    const set = declared.get(appliesToLine) || new Set();
    set.add(code);
    declared.set(appliesToLine, set);
  }
  return declared;
}

/** Return null on success, else a human-readable failure detail comparing
 *  declared directives against raw TH diagnostics produced by
 *  `thales --ignore-expect-error`. */
function verifyDirectiveCoverage(declared, rawDiags) {
  const byLine = new Map();
  for (const d of rawDiags) {
    if (!d.code.startsWith('TH')) continue;
    const n = Number(d.code.slice(2));
    const set = byLine.get(d.line) || new Set();
    set.add(n);
    byLine.set(d.line, set);
  }
  const problems = [];
  const fmtCode = (c) => 'TH' + String(c).padStart(4, '0');
  for (const [line, codes] of declared) {
    const actual = byLine.get(line) || new Set();
    for (const expected of codes) {
      if (expected === null) {
        if (actual.size === 0) {
          problems.push(
            `directive on applied line ${line}: code-less directive but no TH fired`,
          );
        }
      } else if (!actual.has(expected)) {
        const actualStr = Array.from(actual).map(fmtCode).join(', ') || 'none';
        problems.push(
          `directive on applied line ${line}: ${fmtCode(expected)} expected but got {${actualStr}}`,
        );
      }
    }
  }
  for (const line of byLine.keys()) {
    if (!declared.has(line)) {
      problems.push(
        `raw TH at line ${line} not covered by any @thales-expect-error directive`,
      );
    }
  }
  return problems.length === 0 ? null : problems.join('\n  ');
}

// ---- inline self-checks (run on every harness invocation; fast) ----

(function selfCheckHelpers() {
  // Directive helpers.
  if (!hasDirectivePure('// @thales-expect-error TH0001\nlet x = 1;')) {
    throw new Error('hasDirectivePure should match simple directive');
  }
  if (hasDirectivePure('let x = 1;\nconsole.log(x);')) {
    throw new Error('hasDirectivePure should not match plain code');
  }
  // Near-miss typos like `@thales-expect-erorr` MUST classify as directive so
  // the directive flow runs and surfaces TH9003 from thales (mirroring
  // Lean's isLooseMatch).
  if (!hasDirectivePure('// @thales-expect-erorr TH0001\nlet x = 1;')) {
    throw new Error('hasDirectivePure should match near-miss prefix (erorr)');
  }
  if (!hasDirectivePure('// @thales_expect_error TH0001\nlet x = 1;')) {
    throw new Error('hasDirectivePure should match underscore variant');
  }

  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'examples-selftest-'));
  try {
    const probe1 = path.join(tmpDir, 'a.ts');
    fs.writeFileSync(
      probe1,
      '// @thales-expect-error TH0001\nlet x = 0; x = 1;\n',
    );
    const decl1 = collectDeclaredDirectives(probe1);
    if (!(decl1.get(2) && decl1.get(2).has(1))) {
      throw new Error(
        `collectDeclaredDirectives: ${JSON.stringify([...decl1])}`,
      );
    }
    const ok = verifyDirectiveCoverage(decl1, [
      { file: 'a.ts', line: 2, column: 1, code: 'TH0001', message: 'x' },
    ]);
    if (ok !== null)
      throw new Error(`verifyDirectiveCoverage should succeed: ${ok}`);
    const badCode = verifyDirectiveCoverage(decl1, [
      { file: 'a.ts', line: 2, column: 1, code: 'TH0002', message: 'x' },
    ]);
    if (badCode === null)
      throw new Error(`verifyDirectiveCoverage should fail on wrong code`);
  } finally {
    try {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    } catch {}
  }
})();

// ---- per-example decision procedure ----

/**
 * Run tsc --noEmit on input.ts via a per-file tsconfig.json written to a
 * temp directory.
 *
 * We cannot pass `--project` together with source files on the tsc CLI, and we
 * cannot pass `paths` via CLI flags (tsc rejects `--paths` with TS6064). The
 * solution is to write a minimal tsconfig that inherits the repo's
 * `compilerOptions` and adds a single `files` entry pointing to the input.
 * This lets tsc resolve `@thales/prelude` paths correctly without any
 * flag-serialisation hazards.
 *
 * The temporary directory is cleaned up synchronously before the function
 * returns.
 */
function runTsc(inputPath) {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'thales-tsc-'));
  try {
    const baseRaw = fs.readFileSync(
      path.join(repoRoot, 'tsconfig.json'),
      'utf8',
    );
    const base = JSON.parse(baseRaw);
    // Override baseUrl to point at the repo root (tsconfig.json's compilerOptions
    // may have a relative "." which is fine when tsconfig lives at the root, but
    // our temp tsconfig lives in os.tmpdir(), so use an absolute path).
    const compilerOptions = {
      ...base.compilerOptions,
      baseUrl: repoRoot,
    };
    const tempConfig = { compilerOptions, files: [inputPath] };
    const tempCfgPath = path.join(tmp, 'tsconfig.json');
    fs.writeFileSync(tempCfgPath, JSON.stringify(tempConfig));
    const r = runCapture('npx', [
      '--no-install',
      'tsc',
      '--project',
      tempCfgPath,
    ]);
    return { ...r, diags: parseDiagnostics(r.stdout) };
  } finally {
    try {
      fs.rmSync(tmp, { recursive: true, force: true });
    } catch {}
  }
}

/** Run thales --no-emit on input.ts. */
function runThc(inputPath) {
  const r = runCapture(thalesBin, ['--no-emit', inputPath]);
  return { ...r, diags: parseDiagnostics(r.stdout) };
}

/** Run thales --no-emit --ignore-expect-error on input.ts. */
function runThcIgnoringDirectives(inputPath) {
  const r = runCapture(thalesBin, [
    '--no-emit',
    '--ignore-expect-error',
    inputPath,
  ]);
  return { ...r, diags: parseDiagnostics(r.stdout) };
}

/** Core per-example outcome. Returns one of:
 *    {kind: 'pass', label: 'accepted'|'tsc-rejected'|'subset-rejected'}
 *    {kind: 'fail', label: 'missing'|'spurious'|'runtime'
 *                       |'tsc-unexpected'|'directive-check'|'directive-coverage',
 *     detail: string}
 */
function evaluateCase(inputPath) {
  if (hasDirective(inputPath)) {
    // Subset-rejected example (with @thales-expect-error directives): tsc must
    // be clean, thales --no-emit must exit 0 silent (directives suppressed all
    // TH), and the declared codes must match what --ignore-expect-error
    // actually produces.
    const tsc = runTsc(inputPath);
    if (tsc.diags.length > 0) {
      return {
        kind: 'fail',
        label: 'tsc-unexpected',
        detail:
          'subset-rejected example should be tsc-clean:\n  ' +
          tsc.diags.map(fmtDiag).join('\n  '),
      };
    }
    const thales = runThc(inputPath);
    // After directives are applied, no TH should remain — that's what the
    // directive contract asserts. Spurious TS codes from thales (emitted when
    // tsc is silent) are tolerated: they reflect thales type-checker
    // incompleteness orthogonal to subset enforcement, and are caught by
    // the accepting-flow's diagnoseAgreement elsewhere.
    const remainingTh = thales.diags.filter((d) => d.code.startsWith('TH'));
    if (remainingTh.length > 0) {
      return {
        kind: 'fail',
        label: 'directive-check',
        detail:
          'thales --no-emit should have no TH diagnostics after directives:\n  ' +
          remainingTh.map(fmtDiag).join('\n  '),
      };
    }
    const rawThc = runThcIgnoringDirectives(inputPath);
    const declared = collectDeclaredDirectives(inputPath);
    const coverageFail = verifyDirectiveCoverage(declared, rawThc.diags);
    if (coverageFail) {
      return {
        kind: 'fail',
        label: 'directive-coverage',
        detail: coverageFail,
      };
    }
    return { kind: 'pass', label: 'subset-rejected' };
  }

  const tsc = runTsc(inputPath);
  const thales = runThc(inputPath);
  const { missing, spurious } = diagnoseAgreement(tsc.diags, thales.diags);

  if (missing.length + spurious.length > 0) {
    const parts = [];
    if (missing.length > 0) {
      parts.push(
        'tsc errors thales did not match:\n  ' +
          missing.map(fmtDiag).join('\n  '),
      );
    }
    if (spurious.length > 0) {
      parts.push(
        'thales TS errors tsc did not produce:\n  ' +
          spurious.map(fmtDiag).join('\n  '),
      );
    }
    return {
      kind: 'fail',
      label: missing.length > 0 ? 'missing' : 'spurious',
      detail: parts.join('\n'),
    };
  }

  if (tsc.diags.length > 0) {
    return { kind: 'pass', label: 'tsc-rejected' };
  }
  if (thales.diags.some((d) => d.code.startsWith('TH'))) {
    return { kind: 'pass', label: 'subset-rejected' };
  }

  const tsx = runTsx(inputPath);
  const ours = runThcThenLean(inputPath);

  // Relaxed throw-iff equivalence for programs that use @thales/prelude.
  //
  // Prelude throwing constructors (asInteger, asNatural, asByte, asBit) raise
  // RangeError at runtime. The emitted Lean mirrors this via the Subtype
  // constructor, which can also panic. The exact error message / exit code may
  // differ between tsx (Node RangeError) and Lean (kernel panic). We therefore
  // require only:
  //   - both exit 0: byte-identity still required (full accepted check below)
  //   - both exit nonzero: throw-iff equivalence holds — PASS as 'both-throw'
  //   - one exits 0, the other nonzero: FAIL (throw asymmetry)
  //
  // For programs that do NOT import from @thales/prelude, strict byte-identity
  // is unchanged.
  if (importsPrelude(inputPath)) {
    const tsxThrew = tsx.code !== 0;
    const oursThrew = ours.code !== 0;
    if (tsxThrew && oursThrew) {
      // Both threw: throw-iff equivalence holds.
      return { kind: 'pass', label: 'both-throw' };
    }
    if (tsxThrew !== oursThrew) {
      return {
        kind: 'fail',
        label: 'throw-asymmetry',
        detail:
          `tsx exited ${tsx.code}, Lean exited ${ours.code} — ` +
          'exactly one side threw; throw-iff equivalence violated',
      };
    }
    // Both exited 0: fall through to byte-identity check below.
  }

  const runtimeDiff = diffRuns(tsx, ours);
  if (runtimeDiff !== null) {
    return { kind: 'fail', label: 'runtime', detail: runtimeDiff };
  }

  return { kind: 'pass', label: 'accepted' };
}

// ---- driver ----

/** Enumerate corpus cases. For `tests/conformance/`, each bucket
 *  subdirectory in `corpusBuckets` is scanned for `.ts` files;
 *  `future/` is skipped (parked fixtures). For
 *  `Test/Examples/fixtures/`, each subdirectory containing `input.ts` is a
 *  case (paired with `expected-outcome.txt`). Returns an array of
 *  {label, inputPath, expectedPath?} ordered by label.
 */
/** Directory membership IS the test specification: each bucket admits
 *  exactly one pass label. A pass outcome with the wrong label (e.g. an
 *  accept/ file that is merely subset-rejected) is a corpus violation, not
 *  a pass — without this, a regression that demotes an accepted example to
 *  subset-rejected would go unnoticed. This single table drives both the
 *  corpus walk and the outcome enforcement, so a bucket cannot be scanned
 *  without its required label. */
const corpusBuckets = {
  accept: 'accepted',
  mirror: 'tsc-rejected',
  reject: 'subset-rejected',
  throws: 'both-throw',
};

function collectCases(rootDir, mode) {
  const cases = [];
  if (mode === 'flat') {
    for (const bucket of Object.keys(corpusBuckets)) {
      const bucketDir = path.join(rootDir, bucket);
      if (!fs.existsSync(bucketDir)) continue;
      const files = fs.readdirSync(bucketDir).sort();
      for (const name of files) {
        if (!name.endsWith('.ts')) continue;
        cases.push({
          label: `${bucket}/${name}`,
          inputPath: path.join(bucketDir, name),
        });
      }
    }
  } else {
    const entries = fs.readdirSync(rootDir).sort();
    for (const name of entries) {
      const dir = path.join(rootDir, name);
      if (!fs.statSync(dir).isDirectory()) continue;
      const inputPath = path.join(dir, 'input.ts');
      if (!fs.existsSync(inputPath)) continue;
      cases.push({
        label: name,
        inputPath,
        expectedPath: path.join(dir, 'expected-outcome.txt'),
      });
    }
  }
  return cases;
}

function runCorpus(rootDir, opts = {}) {
  const cases = collectCases(rootDir, opts.selfTest ? 'subdir' : 'flat');
  let passes = 0;
  let fails = 0;
  for (const c of cases) {
    process.stdout.write(`${c.label}: `);
    let outcome;
    try {
      outcome = evaluateCase(c.inputPath);
    } catch (e) {
      outcome = { kind: 'fail', label: 'crash', detail: e.stack || e.message };
    }
    if (!opts.selfTest && outcome.kind === 'pass') {
      const bucket = c.label.split('/')[0];
      const expected = corpusBuckets[bucket];
      if (outcome.label !== expected) {
        outcome = {
          kind: 'fail',
          label: 'bucket-mismatch',
          detail: `${bucket}/ requires outcome '${expected}', got '${outcome.label}'`,
        };
      }
    }

    if (opts.selfTest) {
      const expected = fs.readFileSync(c.expectedPath, 'utf8').trim();
      const actual = outcome.kind + ':' + outcome.label;
      if (actual === expected) {
        console.log(`OK (${expected})`);
        passes++;
      } else {
        console.log(`FAIL — expected ${expected}, got ${actual}`);
        if (outcome.detail)
          console.log('  ' + outcome.detail.replace(/\n/g, '\n  '));
        fails++;
      }
    } else {
      if (outcome.kind === 'pass') {
        console.log(`ok (${outcome.label})`);
        passes++;
      } else {
        console.log(`FAIL (${outcome.label})`);
        if (outcome.detail)
          console.log('  ' + outcome.detail.replace(/\n/g, '\n  '));
        fails++;
      }
    }
  }
  return { passes, fails };
}

/** Direct harness checks outside the corpus: exit codes and error codes
 *  from specific thales invocations that exercise behavior not expressible
 *  as a single example directory. Returns null on success, else a
 *  human-readable failure detail. */
function runDirectHarnessChecks() {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'examples-direct-'));
  const check = path.join(tmp, 'input.ts');
  fs.writeFileSync(
    check,
    'let x = 0;\n// @thales-expect-error TH0001\nx = 1;\n',
  );
  try {
    // Emit mode should fail with TH9002 and write no .lean sidecar.
    const r = runCapture(thalesBin, ['--overwrite', '-o', tmp, check]);
    const hasTH9002 = parseDiagnostics(r.stdout).some(
      (d) => d.code === 'TH9002',
    );
    if (!hasTH9002 || r.code === 0) {
      return (
        'emit-blocked-by-directive: expected TH9002 and non-zero exit; got ' +
        `exit=${r.code}\n  ` +
        r.stdout
      );
    }
    const leanPath = path.join(tmp, 'Input.lean');
    if (fs.existsSync(leanPath)) {
      return 'emit-blocked-by-directive: .lean file written despite TH9002';
    }
    return null;
  } finally {
    try {
      fs.rmSync(tmp, { recursive: true, force: true });
    } catch {}
  }
}

const args = process.argv.slice(2);
const selfTest = args.includes('--self-test');

const problems = preflight();
if (problems.length > 0) {
  console.error('Preflight failed:');
  for (const p of problems) console.error('  - ' + p);
  process.exit(2);
}

if (selfTest) {
  console.log('Running harness self-test fixtures...\n');
  if (!fs.existsSync(fixturesDir)) {
    console.log(`(no fixtures directory yet at ${fixturesDir})`);
    process.exit(0);
  }
  const { passes, fails } = runCorpus(fixturesDir, { selfTest: true });
  console.log(`\n${passes} passed, ${fails} failed`);
  process.exit(fails > 0 ? 1 : 0);
}

const directFail = runDirectHarnessChecks();
if (directFail) {
  console.error('Direct harness check failed:\n  ' + directFail);
  process.exit(1);
}

console.log('Running conformance corpus...\n');
const { passes, fails } = runCorpus(conformanceDir, { selfTest: false });
console.log(`\n${passes} passed, ${fails} failed`);
process.exit(fails > 0 ? 1 : 0);
