'use strict';

const assert = require('node:assert/strict');
const { reason } = require('..');

const TTY = process.stdout.isTTY;
const C = TTY
  ? { g: '\x1b[32m', r: '\x1b[31m', y: '\x1b[33m', dim: '\x1b[2m', n: '\x1b[0m' }
  : { g: '', r: '', y: '', dim: '', n: '' };

function ok(msg) {
  console.log(`${C.g}OK${C.n} ${msg}`);
}
function info(msg) {
  console.log(`${C.y}==${C.n} ${msg}`);
}
function fail(msg) {
  console.error(`${C.r}FAIL${C.n} ${msg}`);
}

function msNow() {
  return Date.now();
}

function mustMatch(output, re, label) {
  assert.match(output, re, label || `Expected output to match ${re}`);
}

function mustNotMatch(output, re, label) {
  assert.ok(!re.test(output), label || `Expected output NOT to match ${re}`);
}

function countMatches(output, re) {
  // ensure global counting without mutating caller regex
  const flags = re.flags.includes('g') ? re.flags : re.flags + 'g';
  const rg = new RegExp(re.source, flags);
  let c = 0;
  while (rg.exec(output)) c++;
  return c;
}

function mustOccurExactly(output, re, n, label) {
  const c = countMatches(output, re);
  assert.equal(c, n, label || `Expected ${n} matches of ${re}, got ${c}`);
}

const EX = 'http://example.org/';
// Helper to build a URI quickly
const U = (path) => `<${EX}${path}>`;

function parentChainN3(n) {
  // n links => n+1 nodes: n0->n1->...->nN
  let s = '';
  for (let i = 0; i < n; i++) {
    s += `${U(`n${i}`)} ${U('parent')} ${U(`n${i + 1}`)}.\n`;
  }
  s += `
{ ?x ${U('parent')} ?y } => { ?x ${U('ancestor')} ?y }.
{ ?x ${U('parent')} ?y. ?y ${U('ancestor')} ?z } => { ?x ${U('ancestor')} ?z }.
`;
  return s;
}

function subclassChainN3(n) {
  let s = '';
  for (let i = 0; i <= n; i++) {
    s += `${U(`C${i}`)} ${U('sub')} ${U(`C${i + 1}`)}.\n`;
  }
  s += `${U('x')} ${U('type')} ${U('C0')}.\n`;
  s += `{ ?s ${U('type')} ?a. ?a ${U('sub')} ?b } => { ?s ${U('type')} ?b }.\n`;
  return s;
}

function ruleChainN3(n) {
  let s = '';
  for (let i = 0; i < n; i++) {
    s += `{ ${U('s')} ${U(`p${i}`)} ${U('o')}. } => { ${U('s')} ${U(`p${i + 1}`)} ${U('o')}. }.\n`;
  }
  s += `${U('s')} ${U('p0')} ${U('o')}.\n`;
  return s;
}

function binaryTreeParentN3(depth) {
  const maxNode = (1 << (depth + 1)) - 2;
  let s = '';

  for (let i = 0; i <= maxNode; i++) {
    const left = 2 * i + 1;
    const right = 2 * i + 2;
    if (left <= maxNode) s += `${U(`t${i}`)} ${U('parent')} ${U(`t${left}`)}.\n`;
    if (right <= maxNode) s += `${U(`t${i}`)} ${U('parent')} ${U(`t${right}`)}.\n`;
  }

  s += `
{ ?x ${U('parent')} ?y } => { ?x ${U('ancestor')} ?y }.
{ ?x ${U('parent')} ?y. ?y ${U('ancestor')} ?z } => { ?x ${U('ancestor')} ?z }.
`;
  return s;
}

function transitiveClosureN3(pred) {
  return `
{ ?a ${U(pred)} ?b. ?b ${U(pred)} ?c } => { ?a ${U(pred)} ?c }.
`;
}

function reachabilityGraphN3(n) {
  let s = '';
  for (let i = 0; i < n; i++) {
    s += `${U(`g${i}`)} ${U('edge')} ${U(`g${i + 1}`)}.\n`;
  }
  if (n >= 6) {
    s += `${U('g0')} ${U('edge')} ${U('g3')}.\n`;
    s += `${U('g2')} ${U('edge')} ${U('g5')}.\n`;
    s += `${U('g1')} ${U('edge')} ${U('g4')}.\n`;
  }
  s += `
{ ?a ${U('edge')} ?b } => { ?a ${U('reach')} ?b }.
{ ?a ${U('edge')} ?b. ?b ${U('reach')} ?c } => { ?a ${U('reach')} ?c }.
`;
  return s;
}

function diamondSubclassN3() {
  return `
${U('A')} ${U('sub')} ${U('B')}.
${U('A')} ${U('sub')} ${U('C')}.
${U('B')} ${U('sub')} ${U('D')}.
${U('C')} ${U('sub')} ${U('D')}.
${U('x')} ${U('type')} ${U('A')}.

{ ?s ${U('type')} ?a. ?a ${U('sub')} ?b } => { ?s ${U('type')} ?b }.
`;
}

function join3HopN3(k) {
  let s = '';
  for (let i = 0; i < k; i++) {
    s += `${U(`j${i}`)} ${U('p')} ${U(`j${i + 1}`)}.\n`;
  }
  s += `
{ ?x ${U('p')} ?y. ?y ${U('p')} ?z. ?z ${U('p')} ?w } => { ?x ${U('p3')} ?w }.
`;
  return s;
}

function sameAsN3() {
  return `
${U('a')} ${U('sameAs')} ${U('b')}.
${U('a')} ${U('p')} ${U('o')}.

{ ?x ${U('sameAs')} ?y } => { ?y ${U('sameAs')} ?x }.
{ ?x ${U('sameAs')} ?y. ?x ?p ?o } => { ?y ?p ?o }.
`;
}

function ruleBranchJoinN3() {
  return `
${U('s')} ${U('p')} ${U('o')}.

{ ${U('s')} ${U('p')} ${U('o')}. } => { ${U('s')} ${U('q')} ${U('o')}. }.
{ ${U('s')} ${U('p')} ${U('o')}. } => { ${U('s')} ${U('r')} ${U('o')}. }.
{ ${U('s')} ${U('q')} ${U('o')}. ${U('s')} ${U('r')} ${U('o')}. } => { ${U('s')} ${U('qr')} ${U('o')}. }.
`;
}

function bigFactsN3(n) {
  let s = '';
  for (let i = 0; i < n; i++) {
    s += `${U('x')} ${U('p')} ${U(`o${i}`)}.\n`;
  }
  s += `{ ?s ${U('p')} ?o } => { ?s ${U('q')} ?o }.\n`;
  return s;
}

function negativeEntailmentBatchN3(n) {
  let s = '';
  for (let i = 0; i < n; i++) {
    s += `${U('x')} ${U('ok')} ${U(`v${i}`)}.\n`;
  }
  s += `${U('x')} ${U('forbidden')} ${U('boom')}.\n`;
  s += `{ ?s ${U('forbidden')} ?o. } => false.\n`;
  return s;
}

function symmetricTransitiveN3() {
  return `
${U('a')} ${U('friend')} ${U('b')}.
${U('b')} ${U('friend')} ${U('c')}.
${U('c')} ${U('friend')} ${U('d')}.

{ ?x ${U('friend')} ?y } => { ?y ${U('friend')} ?x }.
{ ?a ${U('friend')} ?b } => { ?a ${U('reachFriend')} ?b }.
{ ?a ${U('friend')} ?b. ?b ${U('reachFriend')} ?c } => { ?a ${U('reachFriend')} ?c }.
`;
}

const cases = [
  {
    name: '01 forward rule: p -> q',
    opt: { proofComments: false },
    input: `
{ ${U('s')} ${U('p')} ${U('o')}. } => { ${U('s')} ${U('q')} ${U('o')}. }.
${U('s')} ${U('p')} ${U('o')}.
`,
    expect: [new RegExp(`${EX}s>\\s+<${EX}q>\\s+<${EX}o>\\s*\\.`)],
  },
  {
    name: '02 two-step: p -> q -> r',
    opt: { proofComments: false },
    input: `
{ ${U('s')} ${U('p')} ${U('o')}. } => { ${U('s')} ${U('q')} ${U('o')}. }.
{ ${U('s')} ${U('q')} ${U('o')}. } => { ${U('s')} ${U('r')} ${U('o')}. }.
${U('s')} ${U('p')} ${U('o')}.
`,
    expect: [new RegExp(`${EX}s>\\s+<${EX}r>\\s+<${EX}o>\\s*\\.`)],
  },
  {
    name: '03 join antecedents: (x p y & y p z) -> (x p2 z)',
    opt: { proofComments: false },
    input: `
{ ?x ${U('p')} ?y. ?y ${U('p')} ?z. } => { ?x ${U('p2')} ?z. }.
${U('a')} ${U('p')} ${U('b')}.
${U('b')} ${U('p')} ${U('c')}.
`,
    expect: [new RegExp(`${EX}a>\\s+<${EX}p2>\\s+<${EX}c>\\s*\\.`)],
  },
  {
    name: '04 inverse relation: (x p y) -> (y invp x)',
    opt: { proofComments: false },
    input: `
{ ?x ${U('p')} ?y. } => { ?y ${U('invp')} ?x. }.
${U('alice')} ${U('p')} ${U('bob')}.
`,
    expect: [new RegExp(`${EX}bob>\\s+<${EX}invp>\\s+<${EX}alice>\\s*\\.`)],
  },
  {
    name: '05 subclass rule: type + sub -> inferred type (two-level chain)',
    opt: { proofComments: false },
    input: `
${U('Human')} ${U('sub')} ${U('Mortal')}.
${U('Mortal')} ${U('sub')} ${U('Being')}.
${U('Socrates')} ${U('type')} ${U('Human')}.

{ ?s ${U('type')} ?a. ?a ${U('sub')} ?b } => { ?s ${U('type')} ?b }.
`,
    expect: [
      new RegExp(`${EX}Socrates>\\s+<${EX}type>\\s+<${EX}Mortal>\\s*\\.`),
      new RegExp(`${EX}Socrates>\\s+<${EX}type>\\s+<${EX}Being>\\s*\\.`),
    ],
  },
  {
    name: '06 transitive closure: sub is transitive',
    opt: { proofComments: false },
    input: `
${U('A')} ${U('sub')} ${U('B')}.
${U('B')} ${U('sub')} ${U('C')}.

{ ?a ${U('sub')} ?b. ?b ${U('sub')} ?c } => { ?a ${U('sub')} ?c }.
`,
    expect: [new RegExp(`${EX}A>\\s+<${EX}sub>\\s+<${EX}C>\\s*\\.`)],
  },
  {
    name: '07 symmetric: knows is symmetric',
    opt: { proofComments: false },
    input: `
{ ?x ${U('knows')} ?y } => { ?y ${U('knows')} ?x }.
${U('a')} ${U('knows')} ${U('b')}.
`,
    expect: [new RegExp(`${EX}b>\\s+<${EX}knows>\\s+<${EX}a>\\s*\\.`)],
  },
  {
    name: '08 recursion: ancestor from parent (2 steps)',
    opt: { proofComments: false },
    input: `
${U('a')} ${U('parent')} ${U('b')}.
${U('b')} ${U('parent')} ${U('c')}.

{ ?x ${U('parent')} ?y } => { ?x ${U('ancestor')} ?y }.
{ ?x ${U('parent')} ?y. ?y ${U('ancestor')} ?z } => { ?x ${U('ancestor')} ?z }.
`,
    expect: [new RegExp(`${EX}a>\\s+<${EX}ancestor>\\s+<${EX}c>\\s*\\.`)],
  },
  {
    name: '09 literals preserved: age -> hasAge',
    opt: { proofComments: false },
    input: `
{ ?s ${U('age')} ?n } => { ?s ${U('hasAge')} ?n }.
${U('x')} ${U('age')} "42".
`,
    expect: [new RegExp(`${EX}x>\\s+<${EX}hasAge>\\s+"42"\\s*\\.`)],
  },
  {
    name: '10 API option: opt can be an args array',
    opt: ['--no-proof-comments'],
    input: `
{ ${U('s')} ${U('p')} ${U('o')}. } => { ${U('s')} ${U('q')} ${U('o')}. }.
${U('s')} ${U('p')} ${U('o')}.
`,
    expect: [new RegExp(`${EX}s>\\s+<${EX}q>\\s+<${EX}o>\\s*\\.`)],
    notExpect: [/^#/m],
  },
  {
    name: '11 negative entailment: rule derives false (expect exit 2 => throws)',
    opt: { proofComments: false },
    input: `
{ ${U('a')} ${U('p')} ${U('b')}. } => false.
${U('a')} ${U('p')} ${U('b')}.
`,
    expectErrorCode: 2,
  },
  {
    name: '12 invalid syntax should throw (non-zero exit)',
    opt: { proofComments: false },
    input: `
@prefix :  # missing dot on purpose
: s :p :o .
`,
    expectError: true,
  },
  {
    name: '13 heavier recursion: ancestor closure over 15 links',
    opt: { proofComments: false, maxBuffer: 200 * 1024 * 1024 },
    input: parentChainN3(15),
    expect: [
      new RegExp(`${EX}n0>\\s+<${EX}ancestor>\\s+<${EX}n15>\\s*\\.`),
      new RegExp(`${EX}n3>\\s+<${EX}ancestor>\\s+<${EX}n12>\\s*\\.`),
    ],
  },
  {
    name: '14 heavier taxonomy: 60-step subclass chain',
    opt: { proofComments: false, maxBuffer: 200 * 1024 * 1024 },
    input: subclassChainN3(60),
    expect: [new RegExp(`${EX}x>\\s+<${EX}type>\\s+<${EX}C61>\\s*\\.`)],
  },
  {
    name: '15 heavier chaining: 40-step predicate rewrite chain',
    opt: { proofComments: false, maxBuffer: 200 * 1024 * 1024 },
    input: ruleChainN3(40),
    expect: [new RegExp(`${EX}s>\\s+<${EX}p40>\\s+<${EX}o>\\s*\\.`)],
  },
  {
    name: '16 heavier recursion: binary tree ancestor closure (depth 4)',
    opt: { proofComments: false, maxBuffer: 200 * 1024 * 1024 },
    input: binaryTreeParentN3(4),
    expect: [
      new RegExp(`${EX}t0>\\s+<${EX}ancestor>\\s+<${EX}t30>\\s*\\.`),
      new RegExp(`${EX}t1>\\s+<${EX}ancestor>\\s+<${EX}t22>\\s*\\.`),
    ],
  },
  {
    name: '17 heavier reachability: branching graph reach closure',
    opt: { proofComments: false, maxBuffer: 200 * 1024 * 1024 },
    input: reachabilityGraphN3(12),
    expect: [
      new RegExp(`${EX}g0>\\s+<${EX}reach>\\s+<${EX}g12>\\s*\\.`),
      new RegExp(`${EX}g2>\\s+<${EX}reach>\\s+<${EX}g10>\\s*\\.`),
    ],
  },
  {
    name: '18 heavier taxonomy: diamond subclass inference',
    opt: { proofComments: false },
    input: diamondSubclassN3(),
    expect: [new RegExp(`${EX}x>\\s+<${EX}type>\\s+<${EX}D>\\s*\\.`)],
  },
  {
    name: '19 heavier join: 3-hop path rule over a chain of 25 edges',
    opt: { proofComments: false, maxBuffer: 200 * 1024 * 1024 },
    input: join3HopN3(25),
    expect: [
      new RegExp(`${EX}j0>\\s+<${EX}p3>\\s+<${EX}j3>\\s*\\.`),
      new RegExp(`${EX}j10>\\s+<${EX}p3>\\s+<${EX}j13>\\s*\\.`),
      new RegExp(`${EX}j20>\\s+<${EX}p3>\\s+<${EX}j23>\\s*\\.`),
    ],
  },
  {
    name: '20 heavier branching: p produces q and r, then q+r produces qr',
    opt: { proofComments: false },
    input: ruleBranchJoinN3(),
    expect: [new RegExp(`${EX}s>\\s+<${EX}qr>\\s+<${EX}o>\\s*\\.`)],
  },
  {
    name: '21 heavier equivalence: sameAs propagation (with symmetric sameAs)',
    opt: { proofComments: false },
    input: sameAsN3(),
    expect: [
      new RegExp(`${EX}b>\\s+<${EX}p>\\s+<${EX}o>\\s*\\.`),
      new RegExp(`${EX}b>\\s+<${EX}sameAs>\\s+<${EX}a>\\s*\\.`),
    ],
  },
  {
    name: '22 heavier closure: transitive property via generic rule',
    opt: { proofComments: false },
    input: `
${U('a')} ${U('sub')} ${U('b')}.
${U('b')} ${U('sub')} ${U('c')}.
${U('c')} ${U('sub')} ${U('d')}.
${U('d')} ${U('sub')} ${U('e')}.
${transitiveClosureN3('sub')}
`,
    expect: [
      new RegExp(`${EX}a>\\s+<${EX}sub>\\s+<${EX}e>\\s*\\.`),
      new RegExp(`${EX}b>\\s+<${EX}sub>\\s+<${EX}d>\\s*\\.`),
    ],
  },
  {
    name: '23 heavier social: symmetric + reachFriend closure',
    opt: { proofComments: false, maxBuffer: 200 * 1024 * 1024 },
    input: symmetricTransitiveN3(),
    expect: [
      new RegExp(`${EX}a>\\s+<${EX}reachFriend>\\s+<${EX}d>\\s*\\.`),
      new RegExp(`${EX}d>\\s+<${EX}reachFriend>\\s+<${EX}a>\\s*\\.`),
    ],
  },
  {
    name: '24 heavier volume: 400 facts, simple rewrite rule p -> q',
    opt: { proofComments: false, maxBuffer: 200 * 1024 * 1024 },
    input: bigFactsN3(400),
    expect: [
      new RegExp(`${EX}x>\\s+<${EX}q>\\s+<${EX}o0>\\s*\\.`),
      new RegExp(`${EX}x>\\s+<${EX}q>\\s+<${EX}o399>\\s*\\.`),
    ],
  },
  {
    name: '25 heavier negative entailment: batch + forbidden => false (expect exit 2)',
    opt: { proofComments: false, maxBuffer: 200 * 1024 * 1024 },
    input: negativeEntailmentBatchN3(200),
    expectErrorCode: 2,
  },
  {
    name: '26 sanity: no rules => no newly derived facts',
    opt: { proofComments: false },
    input: `
${U('a')} ${U('p')} ${U('b')}.
`,
    expect: [/^\s*$/],
  },
  {
    name: '27 regression: backward rule (<=) can satisfy a forward rule premise',
    opt: { proofComments: false },
    input: `
${U('a')} ${U('p')} ${U('b')}.

{ ${U('a')} ${U('q')} ${U('b')}. } <= { ${U('a')} ${U('p')} ${U('b')}. }.
{ ${U('a')} ${U('q')} ${U('b')}. } => { ${U('a')} ${U('r')} ${U('b')}. }.
`,
    expect: [new RegExp(`${EX}a>\\s+<${EX}r>\\s+<${EX}b>\\s*\\.`)],
  },
  {
    name: '28 regression: top-level log:implies behaves like a forward rule',
    opt: { proofComments: false },
    input: `
@prefix log: <http://www.w3.org/2000/10/swap/log#> .

{ ${U('a')} ${U('p')} ${U('b')}. } log:implies { ${U('a')} ${U('q')} ${U('b')}. }.
${U('a')} ${U('p')} ${U('b')}.
`,
    expect: [new RegExp(`${EX}a>\\s+<${EX}q>\\s+<${EX}b>\\s*\\.`)],
  },
  {
    name: '29 regression: derived log:implies becomes a live rule during reasoning',
    opt: { proofComments: false },
    input: `
@prefix log: <http://www.w3.org/2000/10/swap/log#> .

{ ${U('a')} ${U('trigger')} ${U('go')}. }
  =>
{ { ${U('a')} ${U('p')} ${U('b')}. } log:implies { ${U('a')} ${U('q2')} ${U('b')}. }. }.

${U('a')} ${U('trigger')} ${U('go')}.
${U('a')} ${U('p')} ${U('b')}.
`,
    expect: [new RegExp(`${EX}a>\\s+<${EX}q2>\\s+<${EX}b>\\s*\\.`)],
  },
  {
    name: '30 sanity: proofComments:true enables proof comments',
    opt: { proofComments: true },
    input: `
{ ${U('s')} ${U('p')} ${U('o')}. } => { ${U('s')} ${U('q')} ${U('o')}. }.
${U('s')} ${U('p')} ${U('o')}.
`,
    expect: [/^#/m, new RegExp(`${EX}s>\\s+<${EX}q>\\s+<${EX}o>\\s*\\.`)],
  },
  {
    name: '31 sanity: -n suppresses proof comments',
    opt: ['-n'],
    input: `
{ ${U('s')} ${U('p')} ${U('o')}. } => { ${U('s')} ${U('q')} ${U('o')}. }.
${U('s')} ${U('p')} ${U('o')}.
`,
    expect: [new RegExp(`${EX}s>\\s+<${EX}q>\\s+<${EX}o>\\s*\\.`)],
    notExpect: [/^#/m],
  },

  // -------------------------
  // Added sanity/regression tests
  // -------------------------

  {
    name: '32 sanity: variable rule fires for multiple matching facts',
    opt: { proofComments: false },
    input: `
${U('a')} ${U('p')} ${U('b')}.
${U('c')} ${U('p')} ${U('d')}.

{ ?s ${U('p')} ?o. } => { ?s ${U('q')} ?o. }.
`,
    expect: [
      new RegExp(`${EX}a>\\s+<${EX}q>\\s+<${EX}b>\\s*\\.`),
      new RegExp(`${EX}c>\\s+<${EX}q>\\s+<${EX}d>\\s*\\.`),
    ],
  },

  {
    name: '33 regression: mutual cycle does not echo already-known facts',
    opt: { proofComments: false },
    input: `
${U('s')} ${U('p')} ${U('o')}.

{ ?x ${U('p')} ?y. } => { ?x ${U('q')} ?y. }.
{ ?x ${U('q')} ?y. } => { ?x ${U('p')} ?y. }.
`,
    expect: [new RegExp(`${EX}s>\\s+<${EX}q>\\s+<${EX}o>\\s*\\.`)],
    notExpect: [new RegExp(`${EX}s>\\s+<${EX}p>\\s+<${EX}o>\\s*\\.`)],
  },

  {
    name: '34 sanity: rule that reproduces same triple produces no output',
    opt: { proofComments: false },
    input: `
${U('s')} ${U('p')} ${U('o')}.
{ ${U('s')} ${U('p')} ${U('o')}. } => { ${U('s')} ${U('p')} ${U('o')}. }.
`,
    expect: [/^\s*$/],
  },

  {
    name: '35 regression: fuse from derived fact',
    opt: { proofComments: false },
    input: `
${U('a')} ${U('p')} ${U('b')}.

{ ${U('a')} ${U('p')} ${U('b')}. } => { ${U('a')} ${U('q')} ${U('b')}. }.
{ ${U('a')} ${U('q')} ${U('b')}. } => false.
`,
    expectErrorCode: 2,
  },

  {
    name: '36 sanity: multiple consequents in one rule',
    opt: { proofComments: false },
    input: `
${U('s')} ${U('p')} ${U('o')}.

{ ${U('s')} ${U('p')} ${U('o')}. } => { ${U('s')} ${U('q')} ${U('o')}. ${U('s')} ${U('r')} ${U('o')}. }.
`,
    expect: [
      new RegExp(`${EX}s>\\s+<${EX}q>\\s+<${EX}o>\\s*\\.`),
      new RegExp(`${EX}s>\\s+<${EX}r>\\s+<${EX}o>\\s*\\.`),
    ],
  },

  {
    name: '37 regression: backward chaining can chain (<= then <= then =>)',
    opt: { proofComments: false },
    input: `
${U('a')} ${U('p')} ${U('b')}.

{ ${U('a')} ${U('q')} ${U('b')}. } <= { ${U('a')} ${U('p')} ${U('b')}. }.
{ ${U('a')} ${U('r')} ${U('b')}. } <= { ${U('a')} ${U('q')} ${U('b')}. }.
{ ${U('a')} ${U('r')} ${U('b')}. } => { ${U('a')} ${U('s')} ${U('b')}. }.
`,
    expect: [new RegExp(`${EX}a>\\s+<${EX}s>\\s+<${EX}b>\\s*\\.`)],
  },

  {
    name: '38 regression: backward rule body can require multiple facts',
    opt: { proofComments: false },
    input: `
${U('a')} ${U('p')} ${U('b')}.
${U('a')} ${U('p2')} ${U('b')}.

{ ${U('a')} ${U('q')} ${U('b')}. } <= { ${U('a')} ${U('p')} ${U('b')}. ${U('a')} ${U('p2')} ${U('b')}. }.
{ ${U('a')} ${U('q')} ${U('b')}. } => { ${U('a')} ${U('r')} ${U('b')}. }.
`,
    expect: [new RegExp(`${EX}a>\\s+<${EX}r>\\s+<${EX}b>\\s*\\.`)],
  },

  {
    name: '39 sanity: backward rule fails when a required fact is missing',
    opt: { proofComments: false },
    input: `
${U('a')} ${U('p')} ${U('b')}.

{ ${U('a')} ${U('q')} ${U('b')}. } <= { ${U('a')} ${U('p')} ${U('b')}. ${U('a')} ${U('p2')} ${U('b')}. }.
{ ${U('a')} ${U('q')} ${U('b')}. } => { ${U('a')} ${U('r')} ${U('b')}. }.
`,
    expect: [/^\s*$/],
  },

  {
    name: '40 sanity: comments and whitespace are tolerated',
    opt: { proofComments: false },
    input: `
# leading comment
{ ${U('s')} ${U('p')} ${U('o')}. } => { ${U('s')} ${U('q')} ${U('o')}. }.  # trailing comment

${U('s')} ${U('p')} ${U('o')}. # another trailing comment
`,
    expect: [new RegExp(`${EX}s>\\s+<${EX}q>\\s+<${EX}o>\\s*\\.`)],
  },

  {
    name: '41 stability: diamond subclass derives D only once',
    opt: { proofComments: false },
    input: diamondSubclassN3(),
    expect: [new RegExp(`${EX}x>\\s+<${EX}type>\\s+<${EX}D>\\s*\\.`)],
    // and ensure it doesn't print the same derived triple twice via the two paths
    check(out) {
      const reD = new RegExp(`${EX}x>\\s+<${EX}type>\\s+<${EX}D>\\s*\\.`, 'm');
      mustOccurExactly(out, reD, 1, 'diamond subclass should not duplicate x type D');
    },
  },
];

let passed = 0;
let failed = 0;

(async function main() {
  const suiteStart = Date.now();
  info(`Running ${cases.length} API tests (independent of examples/)`);

  for (const tc of cases) {
    const start = msNow();
    try {
      const out = reason(tc.opt, tc.input);

      if (tc.expectErrorCode != null || tc.expectError) {
        throw new Error(`Expected an error, but reason() returned output:\n${out}`);
      }

      for (const re of tc.expect || []) mustMatch(out, re, `${tc.name}: missing expected pattern ${re}`);
      for (const re of tc.notExpect || []) mustNotMatch(out, re, `${tc.name}: unexpected pattern ${re}`);

      if (typeof tc.check === 'function') tc.check(out);

      const dur = msNow() - start;
      ok(`${tc.name} ${C.dim}(${dur} ms)${C.n}`);
      passed++;
    } catch (e) {
      const dur = msNow() - start;

      if (tc.expectErrorCode != null) {
        if (e && typeof e === 'object' && 'code' in e && e.code === tc.expectErrorCode) {
          ok(`${tc.name} ${C.dim}(expected exit ${tc.expectErrorCode}, ${dur} ms)${C.n}`);
          passed++;
          continue;
        }
        fail(`${tc.name} ${C.dim}(${dur} ms)${C.n}`);
        fail(
          `Expected exit code ${tc.expectErrorCode}, got: ${e && e.code != null ? e.code : 'unknown'}\n${
            e && e.stderr ? e.stderr : e && e.stack ? e.stack : String(e)
          }`
        );
        failed++;
        continue;
      }

      if (tc.expectError) {
        ok(`${tc.name} ${C.dim}(expected error, ${dur} ms)${C.n}`);
        passed++;
        continue;
      }

      fail(`${tc.name} ${C.dim}(${dur} ms)${C.n}`);
      fail(e && e.stack ? e.stack : String(e));
      failed++;
    }
  }

  console.log('');
  const suiteMs = Date.now() - suiteStart;
  console.log(`${C.y}==${C.n} Total elapsed: ${suiteMs} ms`);
  if (failed === 0) {
    ok(`All API tests passed (${passed}/${cases.length})`);
    process.exit(0);
  } else {
    fail(`Some API tests failed (${passed}/${cases.length})`);
    process.exit(1);
  }
})();

