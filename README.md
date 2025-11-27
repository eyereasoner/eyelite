# eyelite

A minimal [Notation3 (N3)](https://notation3.org/) reasoner in Rust.

`eyelite` is meant to be **tiny**, **hackable**, and **close in spirit to EYE** on a small but practical fragment of N3.  
It parses a useful subset of N3 (a superset of Turtle) and does forward + backward chaining over Horn-style rules, with a growing set of N3 built-ins.

---

## Features

### Parsing — practical N3 subset

Supported:

- `@prefix` and `@base`
- Triples with `;` / `,` predicate–object lists
- Variables `?x`
- Blank nodes:
  - Anonymous `[]`
  - Property lists `[ :p :o; :q :r ]`
- Collections `( ... )`
- Quoted formulas `{ ... }`
- Implications:
  - Forward rules `{ P } => { C } .`
  - Backward rules `{ C } <= { P } .`
- Datatyped literals with `^^` (e.g. `"1944-08-21"^^xsd:date`)
- `#` line comments

Non-goals / current limits:

- Not a full W3C N3 grammar (edge-case identifiers, path expressions, explicit quantifiers, etc.)
- Quoted formulas in rules are matched only as **whole formulas**; no internal pattern matching yet
- No proof trees / justifications yet
- Built-ins are intentionally incomplete (only what examples need)

---

## Reasoning model

### Forward + backward chaining

- **Forward chaining to fixpoint** over forward rules (`=>`).
- **Backward chaining** (SLD-style) over backward rules (`<=`) and built-ins.
- Forward-rule premises are proved using:
  - Ground facts
  - Backward rules
  - Built-ins  
  Then the (ground) conclusion triples are added to the fact set.

The command-line tool prints **only newly derived forward facts**, not the original input facts.

---

## Blank nodes and quantification

`eyelite` tries to mimic the usual N3 / EYE intuition:

### 1. Blank nodes in facts

Top-level triples like:

```n3
[] :p :o .
[ :p :o ] :q :r .
```

are parsed as normal RDF blank nodes. They keep stable IDs like `_:b1`, `_:b2` inside the run.

### 2. Blank nodes in rule premises → universals

In rule premises (the left side of `=>` / right side of `<=`):

```n3
{
    _:A rdfs:subClassOf ?B .
    ?S  a  _:A .
} => {
    ?S a ?B .
}.
```

The same applies to property-list syntax:

```n3
{
    ?S a [ rdfs:subClassOf ?B ] .
} => {
    ?S a ?B .
}.
```

### 3. Blank nodes in rule conclusions → existentials

If a blank node appears **only in the rule head**, it is treated as an existential:

```n3
# ----------------
# Existential rule
# ----------------

@prefix : <http://example.org/socrates#>.

:Socrates a :Human.
:Plato   a :Human.

{
    ?S a :Human.
} => {
    ?S :is _:B.
}.
```

Each time this rule fires, `eyelite` creates a fresh Skolem blank:

```n3
@prefix : <http://example.org/socrates#>.

:Socrates :is _:sk_0 .
:Plato    :is _:sk_1 .
```

Key points:

* Skolem IDs (`_:sk_0`, `_:sk_1`, …) are unique per firing.
* Equal facts up to renaming of Skolem IDs are treated as duplicates and not re-added, to avoid trivial infinite loops.

---

## Inference fuse — `{ ... } => false.`

`eyelite` treats rules whose conclusion is `false` as **hard failures**:

```n3
# inference fuse

@prefix : <https://eyereasoner.github.io/ns#>.

:stone :color :black .
:stone :color :white .

{
    ?X :color :black .
    ?X :color :white .
} => false.
```

Semantics:

* As soon as the premise is provable, the engine:

  * prints a short message about the fuse being triggered, and
  * exits with **status code 2**.
* This mirrors the “fuse” / inconsistency-detection behavior in EYE.

The Makefile treats the non-zero exit code for the `fuse.n3` example as **expected** and still considers the example run successful.

---

## Built-ins (overview)

Built-ins are recognized by expanded IRIs and evaluated during goal proving (backward phase). A very condensed overview:

### `math:` namespace

* Arithmetic on numeric literals (mostly list forms):

  * `math:sum`, `math:product`, `math:difference`, `math:quotient`
  * `math:exponentiation` (also supports solving for the exponent in some cases)
* Unary ops:

  * `math:negation` (sign flip)
  * `math:absoluteValue`
* Trigonometry:

  * `math:sin`, `math:cos`, `math:asin`, `math:acos`
* Comparison:

  * `math:greaterThan`, `math:lessThan`, `math:notLessThan`
    All accept plain numbers and durations (see below).
* Dates & durations:

  * `math:difference` can take `xsd:date` / `xsd:dateTime` and returns an `xsd:duration`.
  * Duration and date values are internally mapped to seconds to allow comparisons.

### `log:` namespace

* `log:equalTo`
* `log:notEqualTo`

### `time:` namespace

* `time:localTime` — SWAP-style:

  * `"" time:localTime ?D.` binds `?D` to the current local time as `xsd:dateTime`.

### `list:` namespace

Operations on (ground) lists:

* `list:append` — concatenate a list of lists.
* `list:firstRest` — split or construct a list from `(first rest)` (supports an internal open-tail representation for some inverse cases).
* `list:member` — membership, bidirectional over ground lists.
* `list:in` — dual of `list:member`.
* `list:length` — length of a list (integer literal).
* `list:map` — pragmatic “map a builtin over a list” helper:

  * `((a b c) math:absoluteValue) list:map (|a| |b| |c|).`
  * Only works when the predicate is itself a builtin and the input list is ground.

For the exact behavior and corner cases, see the `eval_builtin` function in `src/main.rs`.

---

## Project layout

The crate is deliberately small and self-contained:

* `src/main.rs` — everything:

  * lexer
  * parser & AST
  * backward prover
  * forward engine
  * built-ins
  * CLI

Dependencies:

* [`chrono`](https://crates.io/crates/chrono) for `time:localTime` and date/duration built-ins.
* Standard library only otherwise.

---

## Building and running

### Build

```bash
cargo build --release
```

This produces `target/release/eyelite`.

### Run on a single file

```bash
# via cargo
cargo run --release -- examples/socrates.n3

# or directly
target/release/eyelite examples/socrates.n3
```

Output:

* Only **new** forward derivations, as N3/Turtle.
* `rdf:type` is printed as `a`.

---

## Bundled examples

The repo includes a small suite in `examples/` that exercise different features:

* `socrates.n3` — classic subclass inference.
* `existential-rule.n3` — blank nodes in rule heads → existential Skolem constants.
* `fuse.n3` — `{ ... } => false.` inference fuse and exit code 2.
* `taxonomy.n3` — taxonomy / transitive subclass patterns.
* `age.n3` — dates, durations, and age comparison using `time:` and `math:` built-ins.
* `french-cities.n3` — simple data & rules over a tiny city dataset.
* `gray-code-counter.n3` — Gray code, counters, and list built-ins.
* `hanoi.n3` — recursive Towers of Hanoi rules.
* `lldm.n3` — more advanced reasoning (lists, math).
* `peano.n3` — Peano arithmetic style encodings.
* `backward.n3` — backward rules (`<=`) seeding forward derivations.
* `complex.n3` — combined use of forward / backward rules and built-ins.

(See the `examples` directory and `examples-output.n3` for the full current set.)

### Run all examples

The Makefile contains helper targets:

```bash
# Build optimized binary and run all examples,
# writing their output to examples-output.n3
make run-examples
```

Notes:

* The `fuse.n3` example is expected to trigger the inference fuse and exit with code 2.
* The Makefile treats that specific non-zero exit status as “OK for this example”.

---

## Quick Socrates demo

Minimal RDFS-style subclass inference:

```n3
# ------------------
# Socrates inference
# ------------------

@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
@prefix :    <http://example.org/socrates#>.

# facts
:Socrates a :Human.
:Human    rdfs:subClassOf :Mortal.

# subclass rule
{
    ?A rdfs:subClassOf ?B.
    ?S a ?A.
} => {
    ?S a ?B.
}.
```

Run:

```bash
target/release/eyelite examples/socrates.n3
```

Output:

```n3
@prefix : <http://example.org/socrates#>.

:Socrates a :Mortal .
```

The equivalent formulation with a blank node in the rule body also works:

```n3
{
    _:A rdfs:subClassOf ?B.
    ?S  a _:A.
} => {
    ?S a ?B.
}.
```

and likewise with the inline property list:

```n3
{
    ?S a [ rdfs:subClassOf ?B ] .
} => {
    ?S a ?B .
}.
```

---

## Status and scope

This is **not** a drop-in replacement for EYE:

* No proofs, no query flag, no SPARQL, no streaming, no Euler path tactics.
* Only a small but growing subset of N3 syntax and built-ins.

The aim is:

* A compact, readable Rust codebase that mirrors core N3/EYE ideas:

  * forward + backward rules,
  * universal vs. existential behavior of variables / blank nodes,
  * a few well-chosen built-ins,
  * a notion of inconsistency via `{ ... } => false.`

Contributions, issues, and example PRs are very welcome.

---

## License

MIT License — see `LICENSE` in this repository.

