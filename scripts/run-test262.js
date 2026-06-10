#!/usr/bin/env node
// scripts/run-test262.js
// test262 runner: classifies every test in the sliced directories
// (scripts/test262-slices.json) as skipped / out-of-subset / pass / fail.
// Philosophy, skip buckets, and baseline: docs/test262.md.

import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {
  repoRoot,
  thalesBin,
  parseDiagnostics,
  runCapture,
  runTsx,
  runThcThenLean,
  diffRuns,
  preflight,
} from './lib/harness.js';

const slicesPath = path.join(repoRoot, 'scripts', 'test262-slices.json');
const test262Root = path.join(repoRoot, 'test262');
const shimDir = path.join(repoRoot, 'tests', 'test262', 'harness');

const TYPECHECK_TIMEOUT_MS = 30_000;
const TSX_TIMEOUT_MS = 60_000;
const LEAN_TIMEOUT_MS = 120_000;

// ---- pure helpers ----

/**
 * Parse the YAML frontmatter block (between the canonical frontmatter
 * fences) for the three keys the runner uses. Not a YAML parser: a small
 * line-based extractor for the shapes test262 actually uses (inline
 * `[a, b]` lists, block `- item` lists, the nested `negative:` map).
 * Unknown keys are ignored.
 */
function parseFrontmatter(src) {
  const result = { flags: [], includes: [], negative: null };
  const m = src.match(/\/\*---([\s\S]*?)---\*\//);
  if (!m) return result;
  const lines = m[1].split(/\r?\n/);
  const splitList = (s) =>
    s
      .split(',')
      .map((x) => x.trim())
      .filter((x) => x.length > 0);
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    let kv;
    if ((kv = line.match(/^flags:\s*\[(.*)\]\s*$/))) {
      result.flags = splitList(kv[1]);
    } else if ((kv = line.match(/^includes:\s*\[(.*)\]\s*$/))) {
      result.includes = splitList(kv[1]);
    } else if (/^includes:\s*$/.test(line)) {
      for (let j = i + 1; j < lines.length; j++) {
        const item = lines[j].match(/^\s+-\s*(\S+)\s*$/);
        if (!item) break;
        result.includes.push(item[1]);
      }
    } else if (/^negative:/.test(line)) {
      // Presence alone marks the test negative; phase/type are captured
      // for reporting when the nested form parses.
      result.negative = { phase: '', type: '' };
      for (let j = i + 1; j < lines.length; j++) {
        const sub = lines[j].match(/^\s+(phase|type):\s*(\S+)\s*$/);
        if (!sub) break;
        result.negative[sub[1]] = sub[2];
      }
    }
  }
  return result;
}

/**
 * Skip-bucket decision, in spec order. Returns the bucket name, or null
 * when the test is runnable under the composite scheme. sta.js/assert.js
 * are implicit includes (the shim provides them); anything else is an
 * unported include.
 */
function skipReason(meta) {
  if (meta.negative) return 'negative';
  if (meta.flags.includes('noStrict')) return 'noStrict';
  if (meta.flags.includes('module')) return 'module';
  if (meta.flags.includes('async')) return 'async';
  if (meta.flags.includes('raw')) return 'raw';
  const extra = meta.includes.filter(
    (n) => n !== 'sta.js' && n !== 'assert.js',
  );
  if (extra.length > 0) return 'include:' + extra.sort().join(',');
  return null;
}

/** Number of newline characters in s (= line count when s is
 *  newline-terminated, as the prettier-formatted shim files are). */
function countLines(s) {
  return (s.match(/\n/g) || []).length;
}

/** Attribute a 1-based diagnostic line to the shim or the test body. */
function attributeDiag(line, shimLineCount) {
  return line <= shimLineCount ? 'shim' : 'body';
}

/**
 * Fold per-test outcomes into the report: per-slice and total buckets,
 * plus the blocking-diagnostic histogram (deduped per test by
 * code+attribution, so one noisy test can't dominate).
 */
function aggregate(outcomes) {
  const mkBucket = () => ({
    total: 0,
    skipped: {},
    outOfSubset: 0,
    pass: 0,
    fail: {},
  });
  const slices = {};
  const totals = mkBucket();
  const hist = new Map();
  for (const o of outcomes) {
    const s = (slices[o.slice] ??= mkBucket());
    for (const b of [s, totals]) {
      b.total++;
      if (o.classification === 'skip') {
        b.skipped[o.reason] = (b.skipped[o.reason] || 0) + 1;
      } else if (o.classification === 'out-of-subset') {
        b.outOfSubset++;
      } else if (o.classification === 'pass') {
        b.pass++;
      } else {
        b.fail[o.kind] = (b.fail[o.kind] || 0) + 1;
      }
    }
    if (o.classification === 'out-of-subset') {
      for (const entry of o.codes) {
        const [code, where] = entry.split('@');
        const h = hist.get(code) || { shim: 0, body: 0, unknown: 0 };
        h[where]++;
        hist.set(code, h);
      }
    }
  }
  const finish = (b) => {
    const failTotal = Object.values(b.fail).reduce((x, y) => x + y, 0);
    b.inSubset = b.pass + failTotal;
    b.passRate = b.inSubset > 0 ? b.pass / b.inSubset : null;
  };
  Object.values(slices).forEach(finish);
  finish(totals);
  const histogram = [...hist.entries()]
    .map(([code, h]) => ({ code, ...h, total: h.shim + h.body + h.unknown }))
    .sort((a, b) => b.total - a.total || (a.code < b.code ? -1 : 1));
  return { slices, totals, histogram };
}

// ---- load-time self-checks ----

(function selfCheck() {
  const deepEq = (a, b) => JSON.stringify(a) === JSON.stringify(b);

  // Frontmatter: inline flags list.
  const fm1 = parseFrontmatter(
    '// Copyright\n/*---\nesid: sec-x\ndescription: y\nflags: [onlyStrict, generated]\n---*/\nvar x;\n',
  );
  if (!deepEq(fm1.flags, ['onlyStrict', 'generated']))
    throw new Error(`fm1 flags: ${JSON.stringify(fm1.flags)}`);
  if (!deepEq(fm1.includes, []) || fm1.negative !== null)
    throw new Error('fm1 includes/negative should be empty');

  // Frontmatter: negative with nested phase/type.
  const fm2 = parseFrontmatter(
    '/*---\nnegative:\n  phase: parse\n  type: SyntaxError\n---*/\n',
  );
  if (!fm2.negative || fm2.negative.phase !== 'parse')
    throw new Error(`fm2 negative: ${JSON.stringify(fm2.negative)}`);
  if (fm2.negative.type !== 'SyntaxError')
    throw new Error(`fm2 negative type: ${JSON.stringify(fm2.negative)}`);

  // Frontmatter: includes, inline and block-list forms.
  const fm3 = parseFrontmatter(
    '/*---\nincludes: [propertyHelper.js, sta.js]\n---*/\n',
  );
  if (!deepEq(fm3.includes, ['propertyHelper.js', 'sta.js']))
    throw new Error(`fm3 includes: ${JSON.stringify(fm3.includes)}`);
  const fm4 = parseFrontmatter(
    '/*---\nincludes:\n  - compareArray.js\n---*/\n',
  );
  if (!deepEq(fm4.includes, ['compareArray.js']))
    throw new Error(`fm4 includes: ${JSON.stringify(fm4.includes)}`);

  // Frontmatter: absent entirely.
  const fm5 = parseFrontmatter('var x = 1;\n');
  if (!deepEq(fm5, { flags: [], includes: [], negative: null }))
    throw new Error(`fm5: ${JSON.stringify(fm5)}`);

  // Skip classification, in spec bucket order.
  const meta = (over) => ({ flags: [], includes: [], negative: null, ...over });
  const checks = [
    [
      meta({
        negative: { phase: 'parse', type: 'SyntaxError' },
        flags: ['noStrict'],
      }),
      'negative',
    ],
    [meta({ flags: ['noStrict', 'module'] }), 'noStrict'],
    [meta({ flags: ['module'] }), 'module'],
    [meta({ flags: ['async'] }), 'async'],
    [meta({ flags: ['raw'] }), 'raw'],
    [meta({ includes: ['propertyHelper.js'] }), 'include:propertyHelper.js'],
    [meta({ includes: ['sta.js', 'assert.js'] }), null],
    [meta({ flags: ['onlyStrict'] }), null],
  ];
  for (const [m, want] of checks) {
    const got = skipReason(m);
    if (got !== want)
      throw new Error(
        `skipReason(${JSON.stringify(m)}) = ${got}, want ${want}`,
      );
  }

  // Shim-line attribution arithmetic. A shim of prologue + 2-line sta +
  // 1-line assert spans lines 1..4; the body starts at line 5.
  const shim = '"use strict";\n' + 'line a\nline b\n' + 'line c\n';
  if (countLines(shim) !== 4)
    throw new Error(`countLines: ${countLines(shim)}`);
  if (attributeDiag(4, 4) !== 'shim' || attributeDiag(5, 4) !== 'body')
    throw new Error('attributeDiag boundary wrong');

  // Report aggregation.
  const rep = aggregate([
    { slice: 's', classification: 'skip', reason: 'negative' },
    { slice: 's', classification: 'skip', reason: 'negative' },
    {
      slice: 's',
      classification: 'out-of-subset',
      codes: ['TH0030@shim', 'TH0001@body'],
    },
    { slice: 's', classification: 'out-of-subset', codes: ['TH0030@shim'] },
    { slice: 's', classification: 'pass' },
    { slice: 's', classification: 'fail', kind: 'runtime' },
    { slice: 't', classification: 'fail', kind: 'timeout' },
  ]);
  const s = rep.slices['s'];
  if (s.total !== 6 || s.skipped['negative'] !== 2 || s.outOfSubset !== 2)
    throw new Error(`aggregate s: ${JSON.stringify(s)}`);
  if (s.pass !== 1 || s.fail['runtime'] !== 1)
    throw new Error(`aggregate s pass/fail: ${JSON.stringify(s)}`);
  if (s.inSubset !== 2 || s.passRate !== 0.5)
    throw new Error(`aggregate s rate: ${JSON.stringify(s)}`);
  if (rep.totals.total !== 7 || rep.totals.inSubset !== 3)
    throw new Error(`aggregate totals: ${JSON.stringify(rep.totals)}`);
  const th30 = rep.histogram.find((h) => h.code === 'TH0030');
  if (!th30 || th30.shim !== 2 || th30.body !== 0 || th30.total !== 2)
    throw new Error(`histogram TH0030: ${JSON.stringify(th30)}`);
  if (rep.histogram[0].code !== 'TH0030')
    throw new Error('histogram should sort by total descending');
  // A fail counts toward inSubset, so slice t has inSubset 1, passRate 0.
  // (A slice with NO runnable tests must report passRate null, never NaN —
  // the finish() guard in aggregate handles inSubset === 0.)
  if (rep.slices['t'].inSubset !== 1 || rep.slices['t'].passRate !== 0)
    throw new Error(`aggregate t: ${JSON.stringify(rep.slices['t'])}`);
})();

console.log('self-checks passed (driver lands in the next commit)');
