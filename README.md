# eyeling

A minimal [Notation3 (N3)](https://notation3.org/) reasoner in **JavaScript**.

`eyeling` is:

- a single self-contained file (`eyeling.js`, no external deps)
- intentionally tiny and close in spirit to EYE
- a practical N3/Turtle superset (enough for lots of real rulesets)
- supports forward (`=>`) + backward (`<=`) chaining over Horn-style rules
- prints only newly derived forward facts, optionally preceded by compact proof comments
- “pass-only-new” style output (we never want to leak raw input data; backward rules can act like “functions” over raw data)
- works fully client-side (browser) and in Node.js

## Playground (in your browser)

Try it here:

- [Eyeling playground](https://eyereasoner.github.io/eyeling/demo)

The playground runs `eyeling` client-side. You can:

- edit an N3 program directly
- load an N3 program from a URL
- share a link with the program encoded in the URL fragment (`#...`)

### Example (Socrates)

This link preloads a small “Socrates is Mortal” ruleset:

- [Socrates example](https://eyereasoner.github.io/eyeling/demo#%23%20------------------%0A%23%20Socrates%20inference%0A%23%20------------------%0A%0A%40prefix%20rdfs%3A%20%3Chttp%3A%2F%2Fwww.w3.org%2F2000%2F01%2Frdf-schema%23%3E.%0A%40prefix%20%3A%20%3Chttp%3A%2F%2Fexample.org%2Fsocrates%23%3E.%0A%0A%23%20facts%0A%3ASocrates%20a%20%3AHuman.%0A%3AHuman%20rdfs%3AsubClassOf%20%3AMortal.%0A%0A%23%20subclass%20rule%0A%7B%0A%20%20%20%20%3FS%20a%20%3FA.%0A%20%20%20%20%3FA%20rdfs%3AsubClassOf%20%3FB.%0A%7D%20%3D%3E%20%7B%0A%20%20%20%20%3FS%20a%20%3FB.%0A%7D%2E%0A)

## Quick start (Node.js)

### Requirements

- Node.js >= 18 (anything modern with `BigInt` support is fine)

### Install (npm)

```bash
npm i eyeling
```

### CLI (npm)

Run on a file:

```bash
npx eyeling examples/socrates.n3
```

(Or install globally: `npm i -g eyeling` and run `eyeling ...`.)

### JavaScript API (Node)

```js
const { reason } = require("eyeling");

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
import eyeling from "eyeling";
const output = eyeling.reason({ proofComments: false }, input);
console.log(output);
```

Note: the API currently shells out to the bundled `eyeling.js` CLI under the hood (simple + robust).

## Testing

From a repo checkout:

```bash
npm test
```

Or run individual suites:

```bash
npm run test:api
npm run test:examples
npm run test:package
npm run test:packlist
```

- `test:api` runs an independent JS API test suite (does not rely on `examples/`).
- `test:examples` runs the examples in the `examples` directory and compares against the golden outputs in `examples/output`.
- `test:package` does a “real consumer” smoke test: `npm pack` → install tarball into a temp project → run API + CLI + examples.
- `test:packlist` sanity-checks what will be published in the npm tarball (and the CLI shebang/bin wiring).

### Usage

```
Usage: eyeling.js [options] <file.n3>

Options:
  -h, --help              Show this help and exit.
  -v, --version           Print version and exit.
  -p, --proof-comments    Enable proof explanations.
  -n, --no-proof-comments Disable proof explanations (default).
```

By default, `eyeling`:

1. parses the input (facts + rules)
2. runs **forward chaining to a fixpoint**
3. prints only **newly derived forward facts** (not the original input facts)
4. prints a compact per-triple explanation as `#` comments (can be disabled)

## What output do I get?

For each newly derived triple, `eyeling` prints:

1. a proof-style comment block explaining why the triple holds (unless `-n`), and then
2. the triple itself in N3/Turtle syntax.

The proof comments are compact “local justifications” per derived triple (not a single exported global proof tree).

## Reasoning model

### Forward + backward chaining

- **Forward chaining to fixpoint** for forward rules written as `{ P } => { C } .`
- **Backward chaining (SLD-style)** for backward rules written as `{ H } <= { B } .` and for built-ins.

Forward rule premises are proved using:

- ground facts (input + derived)
- backward rules
- built-ins

The CLI prints only newly derived forward facts.

### Performance notes (current engine)

`eyeling` stays tiny, but includes a few key performance mechanisms:

- facts are indexed for matching:
  - by predicate, and (when possible) by **(predicate, object)** (important for type-heavy workloads)
- duplicate detection uses a fast key path when a triple is fully IRI/Literal-shaped
- backward rules are indexed by head predicate
- the backward prover is **iterative** (explicit stack), so deep chains won’t blow the JS call stack
- for very deep backward chains, substitutions may be compactified (semantics-preserving) to avoid quadratic “copy a growing substitution object” behavior

## Parsing: practical N3 subset

Supported:

- `@prefix` / `@base`
- triples with `;` and `,`
- variables `?x`
- blank nodes:
  - anonymous `[]`
  - property lists `[ :p :o; :q :r ]`
- collections `( ... )`
- quoted formulas `{ ... }`
- implications:
  - forward rules `{ P } => { C } .`
  - backward rules `{ H } <= { B } .`
- datatyped literals with `^^`
- language-tagged string literals: `"hello"@en`, `"colour"@en-GB`
- long string literals: `"""..."""` (can contain newlines; can also carry a language tag)
- inverted predicate sugar: `?x <- :p ?y` (swaps subject/object for that predicate)
- resource paths (forward `!` and reverse `^`): `:joe!:hasAddress!:hasCity "Metropolis".`
- `#` line comments

Non-goals / current limits:

- not a full W3C N3 grammar (some edge cases for identifiers, quantifiers, advanced syntax)
- proof output is local per derived triple (not a global exported proof tree)

## Blank nodes and quantification (pragmatic N3/EYE-style)

`eyeling` follows the usual N3 intuition:

1. blank nodes in facts are normal RDF blanks (`_:b1`, `_:b2`, … within a run)
2. blank nodes in rule premises behave like rule-scoped universals (similar to variables)
3. blank nodes only in rule conclusions behave like existentials: each rule firing generates fresh Skolem blanks (`_:sk_0`, `_:sk_1`, …)

Equal facts up to renaming of Skolem IDs are treated as duplicates and are not re-added.

## Rule-producing rules (meta-rules)

`eyeling` understands the `log:implies` / `log:impliedBy` idiom.

Top level:

- `{ P } log:implies { C } .` becomes a forward rule `{ P } => { C } .`
- `{ H } log:impliedBy { B } .` becomes a backward rule `{ H } <= { B } .`

During reasoning:

- any **derived** `log:implies` / `log:impliedBy` triple with formula subject/object is turned into a new live forward/backward rule.

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

- **crypto**: `crypto:md5` `crypto:sha` `crypto:sha256` `crypto:sha512`
- **list**: `list:append` `list:first` `list:firstRest` `list:in` `list:iterate` `list:last` `list:length` `list:map` `list:member` `list:memberAt` `list:notMember` `list:remove` `list:rest` `list:reverse` `list:sort`
- **log**: `log:collectAllIn` `log:equalTo` `log:forAllIn` `log:impliedBy` `log:implies` `log:notEqualTo` `log:notIncludes` `log:skolem` `log:uri`
- **math**: `math:absoluteValue` `math:acos` `math:asin` `math:atan` `math:cos` `math:cosh` `math:degrees` `math:difference` `math:equalTo` `math:exponentiation` `math:greaterThan` `math:integerQuotient` `math:lessThan` `math:negation` `math:notEqualTo` `math:notGreaterThan` `math:notLessThan` `math:product` `math:quotient` `math:remainder` `math:rounded` `math:sin` `math:sinh` `math:sum` `math:tan` `math:tanh`
- **string**: `string:concatenation` `string:contains` `string:containsIgnoringCase` `string:endsWith` `string:equalIgnoringCase` `string:format` `string:greaterThan` `string:jsonPointer` `string:lessThan` `string:matches` `string:notEqualIgnoringCase` `string:notGreaterThan` `string:notLessThan` `string:notMatches` `string:replace` `string:scrape` `string:startsWith`
- **time**: `time:localTime`

## License

MIT (see [LICENSE](https://github.com/eyereasoner/eyeling/blob/main/LICENSE.md)).

