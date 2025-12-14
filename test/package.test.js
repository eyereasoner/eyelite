#!/usr/bin/env node
'use strict';

const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const cp = require('node:child_process');

const TTY = process.stdout.isTTY;
const C = TTY
  ? { g: '\x1b[32m', r: '\x1b[31m', y: '\x1b[33m', dim: '\x1b[2m', n: '\x1b[0m' }
  : { g: '', r: '', y: '', dim: '', n: '' };

function info(msg) { console.log(`${C.y}==${C.n} ${msg}`); }
function ok(msg)   { console.log(`${C.g}OK${C.n}  ${msg}`); }
function fail(msg) { console.error(`${C.r}FAIL${C.n} ${msg}`); }

function isWin() { return process.platform === 'win32'; }
function npmCmd() { return isWin() ? 'npm.cmd' : 'npm'; }

function rmrf(p) {
  try { fs.rmSync(p, { recursive: true, force: true }); } catch {}
}

function run(cmd, args, opts = {}) {
  const res = cp.spawnSync(cmd, args, {
    encoding: 'utf8',
    maxBuffer: 200 * 1024 * 1024,
    ...opts,
  });
  return res;
}

function runChecked(cmd, args, opts = {}) {
  // Print the command in a dim style
  console.log(`${C.dim}$ ${cmd} ${args.join(' ')}${C.n}`);
  const res = run(cmd, args, opts);
  if (res.error) throw res.error;
  if (res.status !== 0) {
    const err = new Error(`Command failed (${cmd} ${args.join(' ')}), exit ${res.status}`);
    err.code = res.status;
    err.stdout = res.stdout;
    err.stderr = res.stderr;
    throw err;
  }
  return res;
}

function packTarball(root) {
  // `npm pack --silent` prints the filename (usually one line)
  const res = runChecked(npmCmd(), ['pack', '--silent'], { cwd: root });
  const out = String(res.stdout || '').trim().split(/\r?\n/).filter(Boolean);
  if (out.length === 0) throw new Error('npm pack produced no output');
  return out[out.length - 1].trim(); // tarball filename in root
}

function main() {
  const suiteStart = Date.now();
  const root = path.resolve(__dirname, '..');

  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'eyeling-smoke-'));
  const cleanup = () => rmrf(tmp);

  let tgzInRoot = null;

  try {
    info('Building tarball (npm pack)');
    tgzInRoot = packTarball(root);
    const srcTgz = path.join(root, tgzInRoot);
    const dstTgz = path.join(tmp, tgzInRoot);

    fs.renameSync(srcTgz, dstTgz);

    info('Creating temp project + installing tarball');
    runChecked(npmCmd(), ['init', '-y'], { cwd: tmp, stdio: 'ignore' });
    runChecked(npmCmd(), ['install', `./${tgzInRoot}`, '--no-audit', '--no-fund'], { cwd: tmp, stdio: 'inherit' });

    info('API smoke test');
    // Run a tiny API check via node -e
    const apiCode = `
      const { reason } = require('eyeling');
      const input = \`
{ <http://example.org/s> <http://example.org/p> <http://example.org/o>. }
  => { <http://example.org/s> <http://example.org/q> <http://example.org/o>. }.

<http://example.org/s> <http://example.org/p> <http://example.org/o>.
\`;
      const out = reason({ proofComments: false }, input);
      const re = /<http:\\/\\/example\\.org\\/s>\\s+<http:\\/\\/example\\.org\\/q>\\s+<http:\\/\\/example\\.org\\/o>\\s*\\./;
      if (!re.test(out)) {
        console.error('Unexpected output:\\n' + out);
        process.exit(1);
      }
      console.log('OK: API works');
    `;
    runChecked(process.execPath, ['-e', apiCode], { cwd: tmp, stdio: 'inherit' });
    ok('API works');

    info('CLI smoke test');
    const bin = isWin()
      ? path.join(tmp, 'node_modules', '.bin', 'eyeling.cmd')
      : path.join(tmp, 'node_modules', '.bin', 'eyeling');
    runChecked(bin, ['-v'], { cwd: tmp, stdio: 'inherit' });
    ok('CLI works');

    info('Examples test (installed package)');
    const examplesRunner = path.join(tmp, 'node_modules', 'eyeling', 'test', 'examples.test.js');
    runChecked(process.execPath, [examplesRunner], { cwd: tmp, stdio: 'inherit' });
    ok('Installed examples test passed');

    const suiteMs = Date.now() - suiteStart;
    console.log('');
    ok(`Packaged install smoke test passed ${C.dim}(${suiteMs} ms, ${(suiteMs / 1000).toFixed(2)} s)${C.n}`);
    process.exit(0);
  } catch (e) {
    console.log('');
    fail(e && e.stack ? e.stack : String(e));
    process.exit(1);
  } finally {
    // If rename failed and the tarball still exists in root, try to delete it
    if (tgzInRoot) {
      const maybe = path.join(root, tgzInRoot);
      if (fs.existsSync(maybe)) {
        try { fs.unlinkSync(maybe); } catch {}
      }
    }
    cleanup();
  }
}

main();

