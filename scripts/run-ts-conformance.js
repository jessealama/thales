#!/usr/bin/env node
/**
 * TypeScript conformance test runner for Thales.
 *
 * Compares thales output against tsc --noEmit on TypeScript
 * conformance tests from microsoft/TypeScript.
 *
 * Usage:
 *   node scripts/run-ts-conformance.js --sample 100
 *   node scripts/run-ts-conformance.js --dir types/conditional
 *   node scripts/run-ts-conformance.js --dir controlFlow
 */

import { execSync } from 'node:child_process';
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const THALES_BIN = path.join(__dirname, '..', '.lake', 'build', 'bin', 'thales');
const TEST_ROOT = path.join(__dirname, '..', 'typescript-tests', 'tests', 'cases', 'conformance');

// Parse args
const args = process.argv.slice(2);
let sampleSize = 0;
let testDir = '';

for (let i = 0; i < args.length; i++) {
  if (args[i] === '--sample' && args[i+1]) sampleSize = parseInt(args[i+1]);
  if (args[i] === '--dir' && args[i+1]) testDir = args[i+1];
}

// Collect test files
function collectTests(dir) {
  const results = [];
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  for (const entry of entries) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      results.push(...collectTests(full));
    } else if (entry.name.endsWith('.ts') && !entry.name.endsWith('.d.ts')) {
      results.push(full);
    }
  }
  return results;
}

const searchDir = testDir ? path.join(TEST_ROOT, testDir) : TEST_ROOT;
if (!fs.existsSync(searchDir)) {
  console.error(`Directory not found: ${searchDir}`);
  process.exit(1);
}

let tests = collectTests(searchDir);

// Sample if requested
if (sampleSize > 0 && sampleSize < tests.length) {
  // Fisher-Yates shuffle, take first N
  for (let i = tests.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [tests[i], tests[j]] = [tests[j], tests[i]];
  }
  tests = tests.slice(0, sampleSize);
}

// Skip tests that use features we definitely don't support.
// Note: the comparison is always between `tsc --strict` and `thales`,
// regardless of a file's internal `// @strict:` directive — the goal is
// agreement under strict-mode semantics, so non-strict directives do not
// exclude a test.
function shouldSkip(filePath) {
  const content = fs.readFileSync(filePath, 'utf8');
  // Skip tests using modules (import/export)
  if (content.match(/^import\s/m) || content.match(/^export\s/m)) return 'modules';
  // Skip tests with @filename directives (multi-file tests)
  if (content.includes('// @filename:')) return 'multi-file';
  // Skip JSX tests
  if (filePath.includes('/jsx/') || content.includes('@jsx')) return 'jsx';
  // Skip decorator tests
  if (filePath.includes('/decorators/') || filePath.includes('/esDecorators/')) return 'decorators';
  // Skip async/generator tests
  if (filePath.includes('/async/') || filePath.includes('/asyncGenerators/') || filePath.includes('/generators/')) return 'async';
  return null;
}

function runCmd(cmd, timeout = 10000) {
  try {
    const output = execSync(cmd, {
      timeout,
      encoding: 'utf8',
      stdio: ['pipe', 'pipe', 'pipe']
    });
    return { exit: 0, stdout: output.trim(), stderr: '' };
  } catch (e) {
    if (e.killed) return { exit: -1, stdout: '', stderr: 'TIMEOUT' };
    return {
      exit: e.status || 1,
      stdout: ((e.stdout || '').toString()).trim(),
      stderr: ((e.stderr || '').toString()).trim(),
    };
  }
}

// Group tests by top 1–2 path segments so e.g. types/primitives, types/conditional
// don't collapse into a single "types" bucket.
function categoryOf(rel) {
  const parts = rel.split('/');
  return parts.length >= 3 ? `${parts[0]}/${parts[1]}` : parts[0];
}

// Run tests
let total = 0, skipped = 0, agree = 0, disagree = 0;
let thalesOnly = 0, tscOnly = 0;
const skipReasons = {};
const disagreements = [];
const byCategory = new Map();

function bump(cat, key) {
  if (!byCategory.has(cat)) {
    byCategory.set(cat, { total: 0, agree: 0, permissive: 0, strict: 0, parseErr: 0 });
  }
  byCategory.get(cat)[key]++;
}

console.log(`Running ${tests.length} conformance tests...\n`);

for (const testFile of tests) {
  const rel = path.relative(TEST_ROOT, testFile);

  const skipReason = shouldSkip(testFile);
  if (skipReason) {
    skipped++;
    skipReasons[skipReason] = (skipReasons[skipReason] || 0) + 1;
    continue;
  }

  total++;

  // Run tsc
  const tsc = runCmd(`npx tsc --noEmit --strict --target es2020 "${testFile}"`);
  const tscOk = tsc.exit === 0;

  // Run thales
  const thales = runCmd(`"${THALES_BIN}" "${testFile}"`);
  const thalesOk = thales.exit === 0;
  const thalesMsg = (thales.stderr || thales.stdout).split('\n')[0];
  const isParseError = thalesMsg.startsWith('Parse error:');

  const cat = categoryOf(rel);
  bump(cat, 'total');

  if (tscOk === thalesOk) {
    agree++;
    bump(cat, 'agree');
  } else {
    disagree++;
    if (thalesOk && !tscOk) {
      // Thales accepts, tsc rejects — thales is too permissive (false negative)
      thalesOnly++;
      bump(cat, 'permissive');
    } else {
      // Thales rejects, tsc accepts — thales is too strict or has a bug (false positive)
      tscOnly++;
      bump(cat, 'strict');
      if (isParseError) bump(cat, 'parseErr');
      if (disagreements.length < 20) {
        disagreements.push({ file: rel, thalesErr: thalesMsg });
      }
    }
  }

  if (total % 50 === 0) {
    process.stdout.write(`  ${total} tested...\r`);
  }
}

console.log('\n======================================================================');
console.log(`TypeScript Conformance Test Results`);
console.log('======================================================================');
console.log(`Total tested:     ${total}`);
console.log(`Skipped:          ${skipped}`);
console.log(`Agreement:        ${agree} (${(agree/total*100).toFixed(1)}%)`);
console.log(`Disagreement:     ${disagree} (${(disagree/total*100).toFixed(1)}%)`);
console.log(`  Thales too permissive (accepts, tsc rejects): ${thalesOnly}`);
console.log(`  Thales too strict/buggy (rejects, tsc accepts): ${tscOnly}`);
console.log('');
console.log('Skip Reasons:');
for (const [reason, count] of Object.entries(skipReasons).sort((a,b) => b[1]-a[1])) {
  console.log(`  ${reason}: ${count}`);
}

if (byCategory.size > 0) {
  const rows = [...byCategory.entries()]
    .map(([cat, s]) => ({ cat, ...s, pct: s.total > 0 ? s.agree / s.total : 0 }))
    .filter((r) => r.total >= 3); // drop categories too small to be meaningful
  rows.sort((a, b) => a.pct - b.pct);
  console.log('\nPer-Category Breakdown (sorted by agreement ascending, min 3 tests):');
  console.log('Category                                 Total  Agree%  Strict  Parse  Permissive');
  console.log('------------------------------------------------------------------------------');
  for (const r of rows) {
    const flag = r.pct < 0.80 ? ' <' : '  ';
    console.log(
      `${flag}${r.cat.padEnd(40)} ${String(r.total).padStart(5)}  ${(r.pct * 100).toFixed(1).padStart(5)}%  ${String(r.strict).padStart(6)}  ${String(r.parseErr).padStart(5)}  ${String(r.permissive).padStart(10)}`
    );
  }
  console.log('\n  < = below 80% agreement');
}

if (disagreements.length > 0) {
  console.log(`\nFirst ${disagreements.length} cases where thales rejects but tsc accepts:`);
  for (const d of disagreements) {
    console.log(`  ${d.file}`);
    console.log(`    ${d.thalesErr}`);
  }
}
