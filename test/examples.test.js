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

function ok(msg)   { console.log(`${C.g}OK${C.n}  ${msg}`); }
function fail(msg) { console.error(`${C.r}FAIL${C.n} ${msg}`); }
function info(msg) { console.log(`${C.y}==${C.n} ${msg}`); }

function padRight(s, n) {
  s = String(s);
  return s.length >= n ? s : (s + ' '.repeat(n - s.length));
}

function padLeft(s, n) {
  s = String(s);
  return s.length >= n ? s : (' '.repeat(n - s.length) + s);
}

function run(cmd, args, opts = {}) {
  return cp.spawnSync(cmd, args, {
    encoding: 'utf8',
    maxBuffer: 200 * 1024 * 1024,
    ...opts,
  });
}

function hasGit() {
  const r = run('git', ['--version']);
  return r.status === 0;
}

function inGitWorktree(cwd) {
  if (!hasGit()) return false;
  const r = run('git', ['rev-parse', '--is-inside-work-tree'], { cwd });
  return r.status === 0 && String(r.stdout).trim() === 'true';
}

// Expectation logic (same as bash version):
// 1) If file contains a comment like: # expect-exit: 2  -> use that
// 2) Else, if it contains "=> false" -> expect exit 2
// 3) Else -> expect exit 0
function expectedExitCode(n3Text) {
  const m = n3Text.match(/^[ \t]*#[: ]*expect-exit:[ \t]*([0-9]+)\b/m);
  if (m) return parseInt(m[1], 10);
  if (/=>\s*false\b/.test(n3Text)) return 2;
  return 0;
}

function getEyelingVersion(nodePath, eyelingJsPath, cwd) {
  const r = run(nodePath, [eyelingJsPath, '-v'], { cwd });
  // eyeling prints version to stdout in your CLI
  const s = (r.stdout || r.stderr || '').trim();
  return s || 'eyeling (unknown version)';
}

function mkTmpFile() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'eyeling-examples-'));
  const file = path.join(dir, 'generated.n3');
  return { dir, file };
}

function rmrf(p) {
  try { fs.rmSync(p, { recursive: true, force: true }); } catch {}
}

function main() {
  const suiteStart = Date.now();

  // package root: .../test/examples.test.js -> root is one level up
  const root = path.resolve(__dirname, '..');
  const examplesDir = path.join(root, 'examples');
  const outputDir = path.join(examplesDir, 'output');
  const eyelingJsPath = path.join(root, 'eyeling.js');
  const nodePath = process.execPath;

  if (!fs.existsSync(examplesDir)) {
    fail(`Missing examples directory: ${examplesDir}`);
    process.exit(1);
  }
  if (!fs.existsSync(eyelingJsPath)) {
    fail(`Missing eyeling.js: ${eyelingJsPath}`);
    process.exit(1);
  }

  const IN_GIT = inGitWorktree(root);

  // Header
  console.log(`${C.y}-------------------------------------------------${C.n}`);
  console.log(`${C.y}running eyeling examples${C.n}`);
  console.log(
    `${C.y}using ${getEyelingVersion(nodePath, eyelingJsPath, root)} and node ${process.version}${C.n}`
  );
  console.log(`${C.y}-------------------------------------------------${C.n}`);
  console.log('');

  // In maintainer mode we write expected outputs (tracked) to examples/output/
  if (IN_GIT) fs.mkdirSync(outputDir, { recursive: true });

  const files = fs.readdirSync(examplesDir)
    .filter(f => f.endsWith('.n3'))
    .sort((a, b) => a.localeCompare(b));

  if (files.length === 0) {
    info('No .n3 files found in examples/');
    process.exit(0);
  }

  let OK = 0;
  let DIFF = 0;

  for (const file of files) {
    const filePath = path.join(examplesDir, file);
    const expectedPath = path.join(outputDir, file); // examples/output/<file>

    const start = Date.now();

    let n3Text = '';
    try {
      n3Text = fs.readFileSync(filePath, 'utf8');
    } catch (e) {
      const ms = Date.now() - start;
      process.stdout.write(padRight(file, 36));
      process.stdout.write(`${C.y}${padLeft(`${ms} ms`, 10)}${C.n} `);
      console.log(`${C.r}DIFF${C.n} (cannot read input: ${e.message})`);
      DIFF++;
      continue;
    }

    const expectedRc = expectedExitCode(n3Text);

    // Decide where to write generated output
    let tmp = null;
    let generatedPath = expectedPath;

    if (!IN_GIT) {
      // npm-installed / no .git: never modify output/ in node_modules
      if (!fs.existsSync(expectedPath)) {
        const ms = Date.now() - start;
        process.stdout.write(padRight(file, 36));
        process.stdout.write(`${C.y}${padLeft(`${ms} ms`, 10)}${C.n} `);
        console.log(`${C.r}MISSING expected output/${file}${C.n}`);
        DIFF++;
        continue;
      }
      tmp = mkTmpFile();
      generatedPath = tmp.file;
    }

    // Run eyeling, capture exit code without aborting the suite
    // We run `node eyeling.js <file>` from examplesDir so relative paths match old behavior.
    const r = run(nodePath, [eyelingJsPath, file], { cwd: examplesDir });
    const rc = (r.status == null) ? 1 : r.status;

    // Write stdout to the chosen output file (expected in git mode, tmp in npm mode)
    try {
      fs.writeFileSync(generatedPath, r.stdout || '', 'utf8');
    } catch (e) {
      const ms = Date.now() - start;
      process.stdout.write(padRight(file, 36));
      process.stdout.write(`${C.y}${padLeft(`${ms} ms`, 10)}${C.n} `);
      console.log(`${C.r}DIFF${C.n} (cannot write output: ${e.message})`);
      DIFF++;
      if (tmp) rmrf(tmp.dir);
      continue;
    }

    const ms = Date.now() - start;

    // Compare outputs
    let diffOk = false;

    if (IN_GIT) {
      // Compare expectedPath against HEAD using git diff
      const d = run('git', ['diff', '--quiet', '--', path.posix.join('output', file)], { cwd: examplesDir });
      diffOk = (d.status === 0);
    } else {
      // Compare expectedPath vs generatedPath without needing a repo
      if (hasGit()) {
        const d = run('git', ['diff', '--no-index', '--quiet', expectedPath, generatedPath], { cwd: examplesDir });
        diffOk = (d.status === 0);
      } else {
        const d = run('diff', ['-u', expectedPath, generatedPath], { cwd: examplesDir });
        diffOk = (d.status === 0);
      }
    }

    // Decide pass/fail
    process.stdout.write(padRight(file, 36));
    process.stdout.write(`${C.y}${padLeft(`${ms} ms`, 10)}${C.n} `);

    if (diffOk && rc === expectedRc) {
      if (rc === 0) {
        console.log(`${C.g}OK${C.n}`);
      } else {
        console.log(`${C.g}OK${C.n} (exit ${rc})`);
      }
      OK++;
    } else {
      if (rc !== expectedRc) {
        console.log(`${C.r}DIFF${C.n} (exit ${rc}, expected ${expectedRc})`);
      } else {
        console.log(`${C.r}DIFF${C.n}`);
      }
      DIFF++;

      // In npm mode, show a diff (nice UX) without modifying node_modules
      if (!IN_GIT) {
        if (hasGit()) {
          const d = run('git', ['diff', '--no-index', expectedPath, generatedPath], { cwd: examplesDir });
          if (d.stdout) process.stdout.write(d.stdout);
          if (d.stderr) process.stderr.write(d.stderr);
        } else {
          const d = run('diff', ['-u', expectedPath, generatedPath], { cwd: examplesDir });
          if (d.stdout) process.stdout.write(d.stdout);
          if (d.stderr) process.stderr.write(d.stderr);
        }
      }
    }

    // cleanup tmp file
    if (tmp) rmrf(tmp.dir);
  }

  console.log('');
  const suiteMs = Date.now() - suiteStart;
  console.log(`${C.y}==${C.n} Total elapsed: ${suiteMs} ms (${(suiteMs / 1000).toFixed(2)} s)`);
  console.log(`${C.y}==${C.n} ${C.g}${OK} OK${C.n}  ${C.r}${DIFF} DIFF${C.n}`);

  process.exit(DIFF === 0 ? 0 : 2);
}

main();

