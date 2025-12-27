#!/usr/bin/env node
'use strict';

const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const cp = require('node:child_process');

const TTY = process.stdout.isTTY;
const C = TTY ? { g: '\x1b[32m', r: '\x1b[31m', y: '\x1b[33m', dim: '\x1b[2m', n: '\x1b[0m' } : { g: '', r: '', y: '', dim: '', n: '' };
const msTag = (ms) => `${C.dim}(${ms} ms)${C.n}`;

function ok(msg) {
  console.log(`${C.g}OK${C.n}  ${msg}`);
}
function fail(msg) {
  console.error(`${C.r}FAIL${C.n} ${msg}`);
}
function info(msg) {
  console.log(`${C.y}==${C.n} ${msg}`);
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

// Expectation logic:
// 1) If file contains:  # expect-exit: N  -> use N
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
  const s = (r.stdout || r.stderr || '').trim();
  return s || 'eyeling (unknown version)';
}

function mkTmpDir() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'eyeling-examples-'));
  return dir;
}

function rmrf(p) {
  try {
    fs.rmSync(p, { recursive: true, force: true });
  } catch {}
}

function showDiff({ IN_GIT, examplesDir, expectedPath, generatedPath, relExpectedPosix }) {
  if (hasGit()) {
    if (IN_GIT) {
      // Show repo diff for the overwritten golden file
      const d = run('git', ['diff', '--', relExpectedPosix], { cwd: examplesDir });
      if (d.stdout) process.stdout.write(d.stdout);
      if (d.stderr) process.stderr.write(d.stderr);
    } else {
      // Show no-index diff between packaged golden and generated tmp
      const d = run('git', ['diff', '--no-index', expectedPath, generatedPath], { cwd: examplesDir });
      // Replace tmp path in output (nice UX)
      if (d.stdout) process.stdout.write(String(d.stdout).replaceAll(generatedPath, 'generated'));
      if (d.stderr) process.stderr.write(String(d.stderr).replaceAll(generatedPath, 'generated'));
    }
  } else {
    // Fallback: diff -u
    const d = run('diff', ['-u', expectedPath, generatedPath], { cwd: examplesDir });
    if (d.stdout) process.stdout.write(d.stdout);
    if (d.stderr) process.stderr.write(d.stderr);
  }
}

function main() {
  const suiteStart = Date.now();

  // test/examples.test.js -> repo root is one level up
  const root = path.resolve(__dirname, '..');
  const examplesDir = path.join(root, 'examples');
  const outputDir = path.join(examplesDir, 'output');
  const eyelingJsPath = path.join(root, 'eyeling.js');
  const nodePath = process.execPath;

  if (!fs.existsSync(examplesDir)) {
    fail(`Cannot find examples directory: ${examplesDir}`);
    process.exit(1);
  }
  if (!fs.existsSync(eyelingJsPath)) {
    fail(`Cannot find eyeling.js: ${eyelingJsPath}`);
    process.exit(1);
  }

  const IN_GIT = inGitWorktree(root);

  const files = fs
    .readdirSync(examplesDir)
    .filter((f) => f.endsWith('.n3'))
    .sort((a, b) => a.localeCompare(b));

  info(`Running ${files.length} examples tests (${IN_GIT ? 'git worktree mode' : 'npm-installed mode'})`);
  console.log(`${C.dim}${getEyelingVersion(nodePath, eyelingJsPath, root)}; node ${process.version}${C.n}`);

  if (files.length === 0) {
    ok('No .n3 files found in examples/');
    process.exit(0);
  }

  // In maintainer mode we overwrite tracked goldens in examples/output/
  if (IN_GIT) fs.mkdirSync(outputDir, { recursive: true });

  let passed = 0;
  let failed = 0;

  for (let i = 0; i < files.length; i++) {
    const idx = String(i + 1).padStart(2, '0');
    const file = files[i];

    const start = Date.now();

    const filePath = path.join(examplesDir, file);
    const expectedPath = path.join(outputDir, file);
    const relExpectedPosix = path.posix.join('output', file); // for git diff inside examplesDir

    let n3Text;
    try {
      n3Text = fs.readFileSync(filePath, 'utf8');
    } catch (e) {
      const ms = Date.now() - start;
      fail(`${idx} ${file} ${msTag(ms)}`);
      fail(`Cannot read input: ${e.message}`);
      failed++;
      continue;
    }

    const expectedRc = expectedExitCode(n3Text);

    // Decide where generated output goes
    let tmpDir = null;
    let generatedPath = expectedPath;

    if (!IN_GIT) {
      // npm-installed / no .git: never modify output/ in node_modules
      if (!fs.existsSync(expectedPath)) {
        const ms = Date.now() - start;
        fail(`${idx} ${file} ${msTag(ms)}`);
        fail(`Missing expected output/${file}`);
        failed++;
        continue;
      }
      tmpDir = mkTmpDir();
      generatedPath = path.join(tmpDir, 'generated.n3');
    }

    // Run eyeling on this file (cwd examplesDir so relative behavior matches old script)
    const outFd = fs.openSync(generatedPath, 'w');

    const r = cp.spawnSync(nodePath, [eyelingJsPath, '-n', file], {
      cwd: examplesDir,
      stdio: ['ignore', outFd, 'pipe'], // stdout -> file, stderr captured
      maxBuffer: 200 * 1024 * 1024,
      encoding: 'utf8',
    });

    fs.closeSync(outFd);

    const rc = r.status == null ? 1 : r.status;

    const ms = Date.now() - start;

    // Compare output
    let diffOk = false;
    if (IN_GIT) {
      const d = run('git', ['diff', '--quiet', '--', relExpectedPosix], { cwd: examplesDir });
      diffOk = d.status === 0;
    } else {
      if (hasGit()) {
        const d = run('git', ['diff', '--no-index', '--quiet', expectedPath, generatedPath], { cwd: examplesDir });
        diffOk = d.status === 0;
      } else {
        const d = run('diff', ['-u', expectedPath, generatedPath], { cwd: examplesDir });
        diffOk = d.status === 0;
      }
    }

    const rcOk = rc === expectedRc;

    if (diffOk && rcOk) {
      if (expectedRc === 0) {
        ok(`${idx} ${file} ${msTag(ms)}`);
      } else {
        ok(`${idx} ${file} (expected exit ${expectedRc}) ${msTag(ms)}`);
      }
      passed++;
    } else {
      fail(`${idx} ${file} ${msTag(ms)}`);
      if (!rcOk) {
        fail(`Exit code ${rc}, expected ${expectedRc}`);
      }
      if (!diffOk) {
        fail('Output differs');
      }

      // Show diffs (both modes), because this is a test runner
      showDiff({
        IN_GIT,
        examplesDir,
        expectedPath,
        generatedPath,
        relExpectedPosix,
      });

      failed++;
    }

    if (tmpDir) rmrf(tmpDir);
  }

  console.log('');
  const suiteMs = Date.now() - suiteStart;
  info(`Total elapsed: ${suiteMs} ms (${(suiteMs / 1000).toFixed(2)} s)`);

  if (failed === 0) {
    ok(`All examples tests passed (${passed}/${files.length})`);
    process.exit(0);
  } else {
    fail(`Some examples tests failed (${passed}/${files.length})`);
    // keep exit code 2 (matches historical behavior of examples/test)
    process.exit(2);
  }
}

main();
