'use strict';

const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const cp = require('node:child_process');

function reason(opt = {}, n3_input = '') {
  if (n3_input == null) n3_input = '';
  if (typeof n3_input !== 'string') {
    throw new TypeError('reason(opt, n3_input): n3_input must be a string');
  }

  // allow passing an args array directly
  if (Array.isArray(opt)) opt = { args: opt };

  const args = [];

  // default: proof comments OFF for API output (machine-friendly)
  // set { proofComments: true } to keep them
  const proofComments =
    (typeof opt.proofComments === 'boolean') ? opt.proofComments :
    (typeof opt.noProofComments === 'boolean') ? !opt.noProofComments :
    false;

  if (!proofComments) args.push('--no-proof-comments'); // CLI already supports this :contentReference[oaicite:1]{index=1}

  if (Array.isArray(opt.args)) args.push(...opt.args);

  const maxBuffer = Number.isFinite(opt.maxBuffer) ? opt.maxBuffer : 50 * 1024 * 1024;

  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'eyeling-'));
  const inputFile = path.join(dir, 'input.n3');

  try {
    fs.writeFileSync(inputFile, n3_input, 'utf8');

    const eyelingPath = path.join(__dirname, 'eyeling.js');
    const res = cp.spawnSync(process.execPath, [eyelingPath, ...args, inputFile], {
      encoding: 'utf8',
      maxBuffer,
    });

    if (res.error) throw res.error;
    if (res.status !== 0) {
      const err = new Error(res.stderr || `eyeling exited with code ${res.status}`);
      err.code = res.status;
      err.stdout = res.stdout;
      err.stderr = res.stderr;
      throw err;
    }
    return res.stdout;
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

module.exports = { reason };
// small interop nicety for ESM default import
module.exports.default = module.exports;

