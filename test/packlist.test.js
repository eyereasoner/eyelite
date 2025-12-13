'use strict';

const assert = require('node:assert/strict');
const cp = require('node:child_process');
const fs = require('node:fs');

const TTY = process.stdout.isTTY;
const C = TTY
  ? { g: '\x1b[32m', r: '\x1b[31m', y: '\x1b[33m', n: '\x1b[0m' }
  : { g: '', r: '', y: '', n: '' };

function ok(msg) { console.log(`${C.g}OK${C.n} ${msg}`); }
function info(msg) { console.log(`${C.y}${msg}${C.n}`); }
function fail(msg) { console.error(`${C.r}FAIL${C.n} ${msg}`); }

try {
  info('Checking packlist + metadata…');

  const pkg = JSON.parse(fs.readFileSync('package.json', 'utf8'));

  assert.ok(pkg.name, 'package.json: name missing');
  assert.ok(pkg.version, 'package.json: version missing');
  assert.equal(pkg.main, './index.js', 'package.json: main should be ./index.js');
  assert.ok(pkg.bin && pkg.bin.eyeling, 'package.json: bin.eyeling missing');

  assert.ok(fs.existsSync('eyeling.js'), 'eyeling.js missing');
  assert.ok(fs.existsSync('index.js'), 'index.js missing');

  const firstLine = fs.readFileSync('eyeling.js', 'utf8').split(/\r?\n/, 1)[0];
  assert.match(firstLine, /^#!\/usr\/bin\/env node\b/, 'eyeling.js should start with "#!/usr/bin/env node"');

  let packJson;
  try {
    packJson = cp.execSync('npm pack --dry-run --json', { encoding: 'utf8' });
  } catch (e) {
    throw new Error('npm pack --dry-run --json failed\n' + (e.stderr || e.message));
  }

  const pack = JSON.parse(packJson)[0];
  const paths = new Set(pack.files.map(f => f.path));

  const mustHave = [
    'package.json',
    'README.md',
    'LICENSE.md',
    'eyeling.js',
    'index.js',
    'examples/test',
  ];

  for (const p of mustHave) assert.ok(paths.has(p), `missing from npm pack: ${p}`);

  assert.ok(
    [...paths].some(p => p.startsWith('examples/output/')),
    'missing from npm pack: examples/output/*'
  );

  ok('packlist + metadata sanity checks passed');
} catch (e) {
  fail(e && e.stack ? e.stack : String(e));
  process.exit(1);
}

