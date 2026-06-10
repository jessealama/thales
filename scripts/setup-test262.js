#!/usr/bin/env node
// scripts/setup-test262.js
// Materialize the test262 submodule: shallow clone + sparse-checkout of
// the harness directory and the slices listed in test262-slices.json.
// Idempotent; run it again after editing the slice list.

import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const repoRoot = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '..',
);
const { slices } = JSON.parse(
  fs.readFileSync(
    path.join(repoRoot, 'scripts', 'test262-slices.json'),
    'utf8',
  ),
);

function run(cmd, args) {
  console.log(`$ ${cmd} ${args.join(' ')}`);
  const r = spawnSync(cmd, args, {
    cwd: repoRoot,
    stdio: 'inherit',
    timeout: 600_000,
  });
  if (r.status !== 0) {
    console.error(`failed (exit ${r.status})`);
    process.exit(1);
  }
}

run('git', ['submodule', 'update', '--init', '--depth', '1', 'test262']);
run('git', ['-C', 'test262', 'sparse-checkout', 'set', 'harness', ...slices]);
console.log('test262 ready.');
