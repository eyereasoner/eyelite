'use strict';

const assert = require('node:assert/strict');
const { reason } = require('..'); // gebruikt package main: ./index.js

const input = `
{ <http://example.org/s> <http://example.org/p> <http://example.org/o>. }
  => { <http://example.org/s> <http://example.org/q> <http://example.org/o>. }.

<http://example.org/s> <http://example.org/p> <http://example.org/o>.
`;

const out = reason({ proofComments: false }, input);

// Verwacht dat de afgeleide triple aanwezig is (tolerant voor formatting)
assert.match(
  out,
  /<http:\/\/example\.org\/s>\s+<http:\/\/example\.org\/q>\s+<http:\/\/example\.org\/o>\s*\./
);

console.log('OK: reason() inferred expected triple');

