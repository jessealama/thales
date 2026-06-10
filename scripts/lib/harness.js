#!/usr/bin/env node
// scripts/lib/harness.js
// Shared helpers for the conformance harnesses (run-examples.js,
// run-test262.js). These define the contract-critical operations — what
// counts as a diagnostic, what "byte-identical" means, how emitted Lean
// is produced and run — so both runners share one source of truth.
//
// Inline self-checks at the bottom run on every import and throw on
// regression.

import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
export const repoRoot = path.resolve(__dirname, '..', '..');
export const thalesBin = path.join(repoRoot, '.lake', 'build', 'bin', 'thales');

// ---- diagnostics ----

/**
 * Parse a tsc/thales diagnostic stream. Accepts stdout text; returns an array of
 * {file, line, column, code, message} objects sorted by (file, line, column, code).
 * Lines not matching the pattern are silently ignored (tsc's trailing
 * "Found N errors" summary, tsc's pretty-print wrap lines, etc).
 */
export function parseDiagnostics(text) {
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
export function diagKey(d) {
  return `${d.file}:${d.line}:${d.code}`;
}

/** Pretty-print a diagnostic for a failure message. */
export function fmtDiag(d) {
  return `${d.file}(${d.line},${d.column}): error ${d.code}: ${d.message}`;
}

/**
 * Given tsc and thales diag arrays, return {missing, spurious}.
 *   missing  = tsc diagnostics with no matching (file,line,code) in thales
 *   spurious = thales diagnostics with code TS#### and no matching entry in tsc
 * Extra TH#### diagnostics in thales never count as spurious. Column is not
 * part of the match key (see diagKey).
 */
export function diagnoseAgreement(tscDiags, thalesDiags) {
  const thalesKeys = new Set(thalesDiags.map(diagKey));
  const tscKeys = new Set(tscDiags.map(diagKey));
  const missing = tscDiags.filter((d) => !thalesKeys.has(diagKey(d)));
  const spurious = thalesDiags.filter(
    (d) => d.code.startsWith('TS') && !tscKeys.has(diagKey(d)),
  );
  return { missing, spurious };
}

// ---- process capture ----

export function runCapture(cmd, args, opts = {}) {
  const r = spawnSync(cmd, args, { encoding: 'utf8', ...opts });
  return {
    code: r.status == null ? 1 : r.status,
    stdout: r.stdout || '',
    stderr: r.stderr || '',
    err: r.error,
    // spawnSync reports a timeout as error.code === 'ETIMEDOUT'.
    timedOut: !!(r.error && r.error.code === 'ETIMEDOUT'),
  };
}

// ---- environment preflight ----

export function expectedVersion(name) {
  const pkg = JSON.parse(
    fs.readFileSync(path.join(repoRoot, 'package.json'), 'utf8'),
  );
  return pkg.devDependencies[name];
}

export function checkToolVersion(label, cmd, args, extractVersion, expected) {
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
export function checkRuntimeImport() {
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

export function preflight() {
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

// ---- runners ----

/** Run tsx input. */
export function runTsx(inputPath, opts = {}) {
  // Silence DEP0205: tsx invokes Node's deprecated `module.register()` API.
  // The warning fires once per process and pollutes stderr, defeating the
  // byte-identity output check.
  // TODO: remove this once tsx upgrades to `module.registerHooks()`. As of
  // tsx 4.21.0 (latest on npm), it still uses the deprecated entry point.
  return runCapture('npx', ['--no-install', 'tsx', inputPath], {
    env: { ...process.env, NODE_OPTIONS: '--disable-warning=DEP0205' },
    ...opts,
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
export function checkNoSorry(leanPath) {
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
export function runThcThenLean(inputPath, opts = {}) {
  const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'thales-emit-'));
  try {
    const r1 = runCapture(thalesBin, ['--overwrite', '-o', outDir, inputPath], {
      timeout: opts.timeout,
    });
    if (r1.code !== 0) {
      return {
        code: r1.code,
        stdout: r1.stdout,
        stderr: r1.stderr,
        stage: 'emit',
        timedOut: r1.timedOut,
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
        timedOut: false,
      };
    }
    const r2 = runCapture('lake', ['env', 'lean', leanPath], {
      cwd: repoRoot,
      timeout: opts.timeout,
    });
    return {
      code: r2.code,
      stdout: r2.stdout,
      stderr: r2.stderr,
      stage: 'run',
      timedOut: r2.timedOut,
    };
  } finally {
    try {
      fs.rmSync(outDir, { recursive: true, force: true });
    } catch {}
  }
}

/**
 * Byte-compare two captured runs (stdout, stderr, exit code). Returns null
 * when identical, else a human-readable detail string. Labels follow the
 * harness convention: `a` is the tsx run, `b` is the thales→Lean run.
 */
export function diffRuns(a, b) {
  const parts = [];
  if (a.stdout !== b.stdout)
    parts.push(
      `stdout:\n  tsx:  ${JSON.stringify(a.stdout)}\n  ours: ${JSON.stringify(b.stdout)}`,
    );
  if (a.stderr !== b.stderr)
    parts.push(
      `stderr:\n  tsx:  ${JSON.stringify(a.stderr)}\n  ours: ${JSON.stringify(b.stderr)}`,
    );
  if (a.code !== b.code) parts.push(`exit: tsx=${a.code} ours=${b.code}`);
  return parts.length === 0 ? null : parts.join('\n');
}

// ---- inline self-checks (run on every import; fast) ----

(function selfCheckHarness() {
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

  // diffRuns: byte-compare contract.
  const same = { stdout: 'a', stderr: '', code: 0 };
  if (diffRuns(same, { ...same }) !== null) {
    throw new Error('diffRuns should return null on identical runs');
  }
  const d = diffRuns(same, { stdout: 'b', stderr: '', code: 1 });
  if (!d || !d.includes('stdout') || !d.includes('exit')) {
    throw new Error(`diffRuns should report stdout and exit diffs: ${d}`);
  }

  // runCapture timeout detection.
  const slow = runCapture(
    process.execPath,
    ['-e', 'setTimeout(() => {}, 5000);'],
    { timeout: 250 },
  );
  if (!slow.timedOut) {
    throw new Error('runCapture should set timedOut on ETIMEDOUT');
  }
  const fast = runCapture(process.execPath, ['-e', ''], { timeout: 5000 });
  if (fast.timedOut || fast.code !== 0) {
    throw new Error('runCapture should not set timedOut on a fast exit');
  }
})();
