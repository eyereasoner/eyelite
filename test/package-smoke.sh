#!/usr/bin/env bash
set -euo pipefail

if [ -t 1 ]; then
  RED=$'\e[31m'; GREEN=$'\e[32m'; YELLOW=$'\e[33m'; NORMAL=$'\e[0m'
else
  RED=""; GREEN=""; YELLOW=""; NORMAL=""
fi

say() { echo -e "${YELLOW}== $* ==${NORMAL}"; }
ok()  { echo -e "${GREEN}OK${NORMAL} $*"; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP="$(mktemp -d)"
cleanup() { rm -rf "$TMP"; }
trap cleanup EXIT

cd "$ROOT"

say "Building tarball"
TGZ="$(npm pack --silent)"
mv "$TGZ" "$TMP/"
cd "$TMP"

say "Installing tarball into temp project"
npm init -y >/dev/null 2>&1
npm install "./$TGZ" >/dev/null 2>&1

say "API smoke test"
node - <<'NODE'
const { reason } = require('eyeling');
const input = `
{ <http://example.org/s> <http://example.org/p> <http://example.org/o>. }
  => { <http://example.org/s> <http://example.org/q> <http://example.org/o>. }.

<http://example.org/s> <http://example.org/p> <http://example.org/o>.
`;
const out = reason({ proofComments: false }, input);
if (!/<http:\/\/example\.org\/s>\s+<http:\/\/example\.org\/q>\s+<http:\/\/example\.org\/o>\s*\./.test(out)) {
  console.error("Unexpected output:\n" + out);
  process.exit(1);
}
NODE
ok "API works"

say "CLI smoke test"
./node_modules/.bin/eyeling -v
ok "CLI works"

say "Examples test (installed package)"
cd node_modules/eyeling/examples
./test

ok "packaged install smoke test passed"

