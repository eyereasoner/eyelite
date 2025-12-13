# eyeling

A minimal [Notation3 (N3)](https://notation3.org/) reasoner in **JavaScript**.

`eyeling` is:

- a single self-contained file (`eyeling.js`, no external deps),
- intentionally tiny and close in spirit to EYE,
- a practical N3/Turtle superset (enough for lots of real rulesets),
- supports forward (`=>`) + backward (`<=`) chaining over Horn-style rules,
- prints only newly derived forward facts, optionally preceded by compact proof comments,
- we never want to leak raw data, hence pass-only-new and backward rules for functions that work with raw data, and of course we also keep all reasoning in the browser.

## Playground (in your browser)

Try it here:

- [Eyeling playground](https://eyereasoner.github.io/eyeling/demo)

The playground runs `eyeling` client-side. You can:
- edit an N3 program directly,
- load an N3 program from a URL,
- share a link with the program encoded in the URL fragment (`#...`).  

### Example (Socrates)

This link preloads a small “Socrates is Mortal” ruleset:

[Socrates example](https://eyereasoner.github.io/eyeling/demo#%23%20------------------%0A%23%20Socrates%20inference%0A%23%20------------------%0A%0A%40prefix%20rdfs%3A%20%3Chttp%3A%2F%2Fwww.w3.org%2F2000%2F01%2Frdf-schema%23%3E.%0A%40prefix%20%3A%20%3Chttp%3A%2F%2Fexample.org%2Fsocrates%23%3E.%0A%0A%23%20facts%0A%3ASocrates%20a%20%3AHuman.%0A%3AHuman%20rdfs%3AsubClassOf%20%3AMortal.%0A%0A%23%20subclass%20rule%0A%7B%0A%20%20%20%20%3FS%20a%20%3FA.%0A%20%20%20%20%3FA%20rdfs%3AsubClassOf%20%3FB.%0A%7D%20%3D%3E%20%7B%0A%20%20%20%20%3FS%20a%20%3FB.%0A%7D%2E%0A)

## Quick start (Node.js)

### Requirements

- A reasonably recent Node.js (anything modern with `BigInt` support is fine).

```md
## Install (npm)

```bash
npm i eyeling
```

## CLI (npm)

Run on a file:

```bash
npx eyeling examples/socrates.n3
```

(Or install globally: `npm i -g eyeling` and run `eyeling ...`.)

## JavaScript API (Node)

```js
const { reason } = require('eyeling');

const input = `
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
@prefix : <http://example.org/socrates#>.

:Socrates a :Human.
:Human rdfs:subClassOf :Mortal.

{ ?S a ?A. ?A rdfs:subClassOf ?B } => { ?S a ?B }.
`;

const output = reason({ proofComments: false }, input);
console.log(output);
```

ESM:

```js
import eyeling from 'eyeling';

const output = eyeling.reason({ proofComments: false }, input);
console.log(output);
```

Note: the API currently shells out to the bundled `eyeling.js` CLI under the hood (simple + robust).

### Run a single file

From the repo root:

```bash
# Option 1: use the shebang (Unix-like)
./eyeling.js examples/socrates.n3

# Option 2: explicit node
node eyeling.js examples/socrates.n3
```

By default, `eyeling`:

1. parses the input (facts + rules),
2. runs **forward chaining to a fixpoint**,
3. prints only **newly derived forward facts** (not the original input facts),
4. prints a compact per-triple explanation as `#` comments (can be disabled).

### Options

```bash
node eyeling.js --version
node eyeling.js -v

# Disable proof comments (print only derived triples)
node eyeling.js --no-proof-comments examples/socrates.n3
node eyeling.js -n examples/socrates.n3
```

### Run all examples

```bash
cd examples
./test
```

This runs `eyeling.js` over each example and compares against the golden outputs in `examples/output`.

## What output do I get?

For each newly derived triple, `eyeling` prints:

1. a proof-style comment block explaining why the triple holds (unless `-n`), and then
2. the triple itself in N3/Turtle syntax.

The proof comments are compact “local justifications” per derived triple (not a single exported global proof tree).

## Reasoning model

### Forward + backward chaining

* **Forward chaining to fixpoint** for forward rules written as `{ P } => { C } .`
* **Backward chaining (SLD-style)** for backward rules written as `{ H } <= { B } .` and for built-ins.

Forward rule premises are proved using:

* ground facts (input + derived),
* backward rules,
* built-ins.

The CLI prints only newly derived forward facts.

### Performance notes (current engine)

`eyeling` stays tiny, but includes a few key performance mechanisms:

* facts are indexed for matching:

  * by predicate, and (when possible) by **(predicate, object)** (important for type-heavy workloads),
* duplicate detection uses a fast key path when a triple is fully IRI/Literal-shaped,
* backward rules are indexed by head predicate,
* the backward prover is **iterative** (explicit stack), so deep chains won’t blow the JS call stack,
* for very deep backward chains, substitutions may be compactified (semantics-preserving) to avoid quadratic “copy a growing substitution object” behavior.

## Parsing: practical N3 subset

Supported:

* `@prefix` / `@base`
* triples with `;` and `,`
* variables `?x`
* blank nodes:

  * anonymous `[]`
  * property lists `[ :p :o; :q :r ]`
  * collections `( ... )`
* quoted formulas `{ ... }`
* implications:

  * forward rules `{ P } => { C } .`
  * backward rules `{ H } <= { B } .`
* datatyped literals with `^^`
* `#` line comments

Non-goals / current limits:

* not a full W3C N3 grammar (some edge cases for identifiers, quantifiers, advanced syntax),
* quoted formulas are matched as whole formulas (no pattern matching inside formulas yet),
* proof output is local per derived triple (not a global exported proof tree).

## Blank nodes and quantification (pragmatic N3/EYE-style)

`eyeling` follows the usual N3 intuition:

1. blank nodes in facts are normal RDF blanks (`_:b1`, `_:b2`, … within a run),
2. blank nodes in rule premises behave like rule-scoped universals (similar to variables),
3. blank nodes only in rule conclusions behave like existentials:
   each rule firing generates fresh Skolem blanks (`_:sk_0`, `_:sk_1`, …).

Equal facts up to renaming of Skolem IDs are treated as duplicates and are not re-added.

## Rule-producing rules (meta-rules)

`eyeling` understands the `log:implies` / `log:impliedBy` idiom:

Top level:

* `{ P } log:implies { C } .` becomes a forward rule `{ P } => { C } .`
* `{ H } log:impliedBy { B } .` becomes a backward rule `{ H } <= { B } .`

During reasoning:

* any **derived** `log:implies` / `log:impliedBy` triple with formula subject/object is turned into a new live forward/backward rule.

## Inference fuse — `{ ... } => false.`

Rules whose conclusion is `false` are treated as hard failures:

```n3
:stone :color :black .
:stone :color :white .
{ ?X :color :black . ?X :color :white . } => false.
```

As soon as the premise is provable, `eyeling` exits with status code `2`.

## Built-ins (overview)

`eyeling` implements a pragmatic subset of common N3 builtin families and evaluates them during backward goal proving:

* **crypto**: `crypto:md5` `crypto:sha` `crypto:sha256` `crypto:sha512`
* **list**: `list:append` `list:first` `list:firstRest` `list:in` `list:iterate` `list:last` `list:length` `list:map` `list:member` `list:memberAt` `list:notMember` `list:remove` `list:reverse` `list:sort`
* **log**: `log:collectAllIn` `log:equalTo` `log:forAllIn` `log:impliedBy` `log:implies` `log:notEqualTo` `log:notIncludes` `log:skolem` `log:uri`
* **math**: `math:absoluteValue` `math:acos` `math:asin` `math:atan` `math:cos` `math:cosh` `math:degrees` `math:difference` `math:equalTo` `math:exponentiation` `math:greaterThan` `math:lessThan` `math:negation` `math:notEqualTo` `math:notGreaterThan` `math:notLessThan` `math:product` `math:quotient` `math:remainder` `math:rounded` `math:sin` `math:sinh` `math:sum` `math:tan` `math:tanh`
* **string**: `string:concatenation` `string:contains` `string:containsIgnoringCase` `string:endsWith` `string:equalIgnoringCase` `string:format` `string:greaterThan` `string:lessThan` `string:matches` `string:notEqualIgnoringCase` `string:notGreaterThan` `string:notLessThan` `string:notMatches` `string:replace` `string:scrape` `string:startsWith`
* **time**: `time:localTime`


## License

MIT (see [LICENSE](https://github.com/eyereasoner/eyeling/blob/main/LICENSE.md)).

