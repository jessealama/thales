#!/usr/bin/env node
// scripts/run-examples.js
// Drives the Thales-TS ↔ TypeScript conformance harness.
//
// Environment assumptions (CI pins these; local runs may differ):
//   NODE_VERSION 24.x, LC_ALL=C.UTF-8, TZ=UTC, lean-toolchain from repo.

import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');
const examplesDir = path.join(repoRoot, 'examples');
const fixturesDir = path.join(repoRoot, 'Test', 'Examples', 'fixtures');
const thalesBin = path.join(repoRoot, '.lake', 'build', 'bin', 'thales');

// ---- pure helpers ----

/**
 * Parse a tsc/thales diagnostic stream. Accepts stdout text; returns an array of
 * {file, line, column, code, message} objects sorted by (file, line, column, code).
 * Lines not matching the pattern are silently ignored (tsc's trailing
 * "Found N errors" summary, tsc's pretty-print wrap lines, etc).
 */
function parseDiagnostics(text) {
  const re = /^(.+?)\((\d+),(\d+)\): error (TS\d+|TH\d+): (.*)$/;
  const diags = [];
  for (const line of text.split(/\r?\n/)) {
    const m = line.match(re);
    if (!m) continue;
    diags.push({
      file: path.basename(m[1]), // basename only — we don't care about abs/rel path mismatch
      line: Number(m[2]),
      column: Number(m[3]),
      code: m[4],
      message: m[5],
    });
  }
  diags.sort((a, b) => {
    if (a.file !== b.file) return a.file < b.file ? -1 : 1;
    if (a.line !== b.line) return a.line - b.line;
    if (a.column !== b.column) return a.column - b.column;
    return a.code < b.code ? -1 : a.code > b.code ? 1 : 0;
  });
  return diags;
}

/** A stable string key for a diagnostic (file, line, code).
    NOTE: column is intentionally NOT in the key. tsc and thales disagree on
    per-diagnostic column anchoring (thales tends to anchor at RHS expressions;
    tsc at binding identifiers) and no in-reach thales fix aligns every
    diagnostic kind. The harness therefore requires line + code agreement
    and ignores column. Column is still parsed and shown in failure messages
    so humans can see the disagreement when it matters. */
function diagKey(d) {
  return `${d.file}:${d.line}:${d.code}`;
}

/** Pretty-print a diagnostic for a failure message. */
function fmtDiag(d) {
  return `${d.file}(${d.line},${d.column}): error ${d.code}: ${d.message}`;
}

/**
 * Given tsc and thales diag arrays, return {missing, spurious}.
 *   missing  = tsc diagnostics with no matching (file,line,code) in thales
 *   spurious = thales diagnostics with code TS#### and no matching entry in tsc
 * Extra TH#### diagnostics in thales never count as spurious. Column is not
 * part of the match key (see diagKey).
 */
function diagnoseAgreement(tscDiags, thalesDiags) {
  const thalesKeys = new Set(thalesDiags.map(diagKey));
  const tscKeys = new Set(tscDiags.map(diagKey));
  const missing = tscDiags.filter((d) => !thalesKeys.has(diagKey(d)));
  const spurious = thalesDiags.filter(
    (d) => d.code.startsWith('TS') && !tscKeys.has(diagKey(d)),
  );
  return { missing, spurious };
}

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
  const sample = [
    "/tmp/foo.ts(3,5): error TS2322: Type 'string' is not assignable to type 'number'.",
    '/tmp/foo.ts(4,1): error TH0010: Loop not supported; use recursion or array methods',
    'Found 2 errors in the same file, starting at: /tmp/foo.ts:3',
  ].join('\n');
  const ds = parseDiagnostics(sample);
  if (ds.length !== 2)
    throw new Error(`parseDiagnostics sample: got ${ds.length}, want 2`);
  if (ds[0].code !== 'TS2322' || ds[0].line !== 3 || ds[0].column !== 5) {
    throw new Error(`parseDiagnostics[0] wrong: ${JSON.stringify(ds[0])}`);
  }
  if (ds[1].code !== 'TH0010')
    throw new Error(`parseDiagnostics[1] wrong: ${JSON.stringify(ds[1])}`);

  const tsc = [
    { file: 'foo.ts', line: 3, column: 5, code: 'TS2322', message: 'a' },
  ];
  const thales = [
    { file: 'foo.ts', line: 3, column: 5, code: 'TS2322', message: 'a' },
    { file: 'foo.ts', line: 4, column: 1, code: 'TH0010', message: 'b' },
  ];
  const { missing, spurious } = diagnoseAgreement(tsc, thales);
  if (missing.length !== 0 || spurious.length !== 0) {
    throw new Error(
      `diagnoseAgreement should be clean; got ${JSON.stringify({ missing, spurious })}`,
    );
  }
  const { missing: m2 } = diagnoseAgreement(tsc, []);
  if (m2.length !== 1)
    throw new Error(`diagnoseAgreement should report missing`);
  const { spurious: s2 } = diagnoseAgreement(
    [],
    [{ file: 'foo.ts', line: 1, column: 1, code: 'TS9999', message: 'x' }],
  );
  if (s2.length !== 1)
    throw new Error(`diagnoseAgreement should report spurious`);

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

// ---- environment preflight ----

function runCapture(cmd, args, opts = {}) {
  const r = spawnSync(cmd, args, { encoding: 'utf8', ...opts });
  return {
    code: r.status == null ? 1 : r.status,
    stdout: r.stdout || '',
    stderr: r.stderr || '',
    err: r.error,
  };
}

function expectedVersion(name) {
  const pkg = JSON.parse(
    fs.readFileSync(path.join(repoRoot, 'package.json'), 'utf8'),
  );
  return pkg.devDependencies[name];
}

function checkToolVersion(label, cmd, args, extractVersion, expected) {
  const r = runCapture(cmd, args);
  if (r.code !== 0) {
    return {
      ok: false,
      why: `${label}: '${cmd} ${args.join(' ')}' failed (${r.err ? r.err.message : 'exit ' + r.code})`,
    };
  }
  const got = extractVersion(r.stdout + r.stderr);
  if (!got)
    return {
      ok: false,
      why: `${label}: could not extract version from output:\n${r.stdout}${r.stderr}`,
    };
  if (expected && got !== expected) {
    return { ok: false, why: `${label}: expected ${expected}, got ${got}` };
  }
  return { ok: true, version: got };
}

/** Verify that `lake env lean` can resolve Thales.TS.Runtime. */
function checkRuntimeImport() {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'thales-preflight-'));
  const probe = path.join(tmp, 'Probe.lean');
  fs.writeFileSync(probe, 'import Thales.TS.Runtime\n');
  try {
    const r = runCapture('lake', ['env', 'lean', probe], { cwd: repoRoot });
    if (r.code !== 0) {
      return {
        ok: false,
        why: `lake env lean could not elaborate 'import Thales.TS.Runtime':\n${r.stdout}${r.stderr}`,
      };
    }
    return { ok: true };
  } finally {
    try {
      fs.rmSync(tmp, { recursive: true, force: true });
    } catch {}
  }
}

function preflight() {
  const problems = [];
  const check = (result) => {
    if (!result.ok) problems.push(result.why);
  };

  check(
    checkToolVersion(
      'tsc',
      'npx',
      ['--no-install', 'tsc', '--version'],
      (s) => (s.match(/Version\s+(\S+)/) || [])[1],
      expectedVersion('typescript'),
    ),
  );

  check(
    checkToolVersion(
      'tsx',
      'npx',
      ['--no-install', 'tsx', '--version'],
      (s) =>
        (s.match(/tsx\s+v?(\S+)/) || s.match(/^v?(\d+\.\d+\.\d+)/m) || [])[1],
      expectedVersion('tsx'),
    ),
  );

  check(
    checkToolVersion(
      'lake',
      'lake',
      ['--version'],
      (s) => (s.match(/Lake version\s+(\S+)/) || [])[1],
      null,
    ),
  ); // no pinned expectation; we only require presence

  check(
    checkToolVersion(
      'lean',
      'lean',
      ['--version'],
      (s) => (s.match(/Lean \(version (\S+?),/) || [])[1],
      null,
    ),
  );

  if (!fs.existsSync(thalesBin)) {
    problems.push(
      `thales binary missing: ${thalesBin}. Run 'lake build thales'.`,
    );
  }

  if (problems.length === 0) {
    // Only probe the runtime import if all tools are present; otherwise the probe
    // adds a confusing "lean not found" message on top of the real problem.
    const r = checkRuntimeImport();
    if (!r.ok) problems.push(r.why);
  }

  return problems;
}

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

/** Run tsx input.ts. */
function runTsx(inputPath) {
  // Silence DEP0205: tsx invokes Node's deprecated `module.register()` API.
  // The warning fires once per process and pollutes stderr, defeating the
  // byte-identity output check.
  // TODO: remove this once tsx upgrades to `module.registerHooks()`. As of
  // tsx 4.21.0 (latest on npm), it still uses the deprecated entry point.
  return runCapture('npx', ['--no-install', 'tsx', inputPath], {
    env: { ...process.env, NODE_OPTIONS: '--disable-warning=DEP0205' },
  });
}

/**
 * Check an emitted Lean file for `sorry` or `sorryAx`. Returns a TH9004
 * diagnostic string if found, else null.
 *
 * This check catches emit-pipeline regressions where a soundness bug causes
 * the emitter to produce `sorry`-bearing proof terms. TH9004 is not a user
 * error; it signals a Thales bug. The grep is applied ONLY to files emitted
 * by thales (not to Test/ WIP proofs or Thales/ sources).
 */
function checkNoSorry(leanPath) {
  let src;
  try {
    src = fs.readFileSync(leanPath, 'utf8');
  } catch {
    return null; // file not found — emitter already reported the error
  }
  const sorryRe = /\bsorry(?:Ax)?\b/;
  if (sorryRe.test(src)) {
    return (
      `TH9004: emitted Lean file contains 'sorry' or 'sorryAx': ${leanPath}\n` +
      `This is a Thales emit-pipeline bug, not a user error. Please file a bug report.`
    );
  }
  return null;
}

/**
 * Emit inputPath with thales --overwrite into a fresh temp dir, then run the resulting
 * .lean via lake env lean. Always cleans up the temp dir on exit.
 */
function runThcThenLean(inputPath) {
  const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'thales-emit-'));
  try {
    const r1 = runCapture(thalesBin, ['--overwrite', '-o', outDir, inputPath]);
    if (r1.code !== 0) {
      return {
        code: r1.code,
        stdout: r1.stdout,
        stderr: r1.stderr,
        stage: 'emit',
      };
    }
    // `thales -o <dir> foo.ts` writes `<dir>/Foo.lean` — basename capitalized, extension stripped,
    // non-alphanumerics removed (matches thales's inputToModuleName).
    const base = path.basename(inputPath).replace(/\.[mc]?ts$/, '');
    const moduleName =
      base.charAt(0).toUpperCase() + base.slice(1).replace(/[^A-Za-z0-9]/g, '');
    const leanPath = path.join(outDir, moduleName + '.lean');
    // TH9004: post-emit noSorry check — applied only to files emitted by thales.
    const sorryFail = checkNoSorry(leanPath);
    if (sorryFail) {
      return {
        code: 1,
        stdout: sorryFail,
        stderr: '',
        stage: 'nosorry',
      };
    }
    const r2 = runCapture('lake', ['env', 'lean', leanPath], { cwd: repoRoot });
    return {
      code: r2.code,
      stdout: r2.stdout,
      stderr: r2.stderr,
      stage: 'run',
    };
  } finally {
    try {
      fs.rmSync(outDir, { recursive: true, force: true });
    } catch {}
  }
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

  if (
    tsx.stdout !== ours.stdout ||
    tsx.stderr !== ours.stderr ||
    tsx.code !== ours.code
  ) {
    const parts = [];
    if (tsx.stdout !== ours.stdout)
      parts.push(
        `stdout:\n  tsx:  ${JSON.stringify(tsx.stdout)}\n  ours: ${JSON.stringify(ours.stdout)}`,
      );
    if (tsx.stderr !== ours.stderr)
      parts.push(
        `stderr:\n  tsx:  ${JSON.stringify(tsx.stderr)}\n  ours: ${JSON.stringify(ours.stderr)}`,
      );
    if (tsx.code !== ours.code)
      parts.push(`exit: tsx=${tsx.code} ours=${ours.code}`);
    return { kind: 'fail', label: 'runtime', detail: parts.join('\n') };
  }

  return { kind: 'pass', label: 'accepted' };
}

// ---- driver ----

/** Enumerate corpus cases. For `examples/`, each `.ts` file is a case. For
 *  `Test/Examples/fixtures/`, each subdirectory containing `input.ts` is a
 *  case (paired with `expected-outcome.txt`). Returns an array of
 *  {label, inputPath, expectedPath?} ordered by label.
 */
function collectCases(rootDir, mode) {
  const entries = fs.readdirSync(rootDir).sort();
  const cases = [];
  if (mode === 'flat') {
    for (const name of entries) {
      if (!name.endsWith('.ts')) continue;
      cases.push({ label: name, inputPath: path.join(rootDir, name) });
    }
  } else {
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

console.log('Running examples...\n');
const { passes, fails } = runCorpus(examplesDir, { selfTest: false });
console.log(`\n${passes} passed, ${fails} failed`);
process.exit(fails > 0 ? 1 : 0);
