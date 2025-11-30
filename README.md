# eyeling

A minimal [Notation3 (N3)](https://notation3.org/) reasoner in Rust.

`eyeling` is meant to be **tiny** and **close in spirit to EYE** on a small but practical fragment of N3. It parses a useful subset of N3 (a superset of Turtle) and does forward + backward chaining over Horn-style rules, with a growing set of N3 built-ins.

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
- Built-ins are intentionally incomplete (only what the examples need)

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

### Rule-producing rules (meta-rules)

`eyeling` understands rules that *produce* other rules, using the `log:implies` / `log:impliedBy` idiom:

- Top level:
  - A triple of the form  
    `( { P } ) log:implies ( { C } ) .`  
    is turned into a forward rule `{ P } => { C } .`
  - A triple of the form  
    `( { H } ) log:impliedBy ( { B } ) .`  
    is turned into a backward rule `{ H } <= { B } .`
- Nested in formulas:
  - Inside a formula `{ ... }`, `A => B` is normalized as  
    `( A ) log:implies ( B )`.
  - Likewise, `A <= B` becomes  
    `( A ) log:impliedBy ( B )`.

During reasoning:

- Any **derived** triple whose predicate is `log:implies` / `log:impliedBy` and whose subject and object are formulas is also turned into a new live rule (forward or backward).
- The triple itself is kept as a fact and printed in `{ ... } => { ... } .` / `{ ... } <= { ... } .` syntax.

This supports EYE-style meta-programs, such as rules that generate subclass-propagation rules, property rules, etc.

### Backward memo-table (tiny cache)

The backward prover uses a small memo table for non-builtin goals during the proof of a forward rule premise:

- When a non-builtin goal is solved once, its solutions are cached.
- Subsequent attempts to solve the *same instantiated goal* re-use the cached solutions instead of re-proving it from scratch.

This doesn’t change semantics, but substantially reduces repeated work in some examples (e.g., numeric recursions, meta-rules) and improves performance overall.

A simple depth limit (`MAX_BACKWARD_DEPTH`) is used as a safety guard against infinite or very deep recursion.

---

## Blank nodes and quantification

`eyeling` tries to mimic the usual N3 / EYE intuition:

### 1. Blank nodes in facts → normal RDF blanks

Top-level triples like:

```n3
[] :p :o .
[ :p :o ] :q :r .
```

are parsed as normal RDF blank nodes. They keep stable IDs like `_:b1`, `_:b2` inside the run.

### 2. Blank nodes in rule premises → universals

In rule premises (the left side of `=>` / right side of `<=`):

```n3
{ _:A rdfs:subClassOf ?B .
  ?S  a              _:A .
} => {
  ?S a ?B .
}.
```

the locally scoped `_:` nodes are treated like **rule-scoped universal variables**:

* `_:A` inside a rule body behaves as if it were written as `?A`.
* Occurrences of the same `_:` label inside that rule premise are linked together.

The same applies to property-list syntax:

```n3
{ ?S a [ rdfs:subClassOf ?B ] . } => { ?S a ?B . }.
```

Here the inlined `[ rdfs:subClassOf ?B ]` introduces a body-local “class” that behaves as a universally quantified variable in that rule.

### 3. Blank nodes in rule conclusions → existentials

If a blank node appears **only in the rule head**, it is treated as an existential:

```n3
@prefix : <http://example.org/socrates#>.

:Socrates a :Human.
:Plato   a :Human.

{ ?S a :Human. } => { ?S :is _:B. }.
```

Each time this rule fires, `eyeling` creates a fresh Skolem blank:

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

`eyeling` treats rules whose conclusion is `false` as **hard failures**:

```n3
# inference fuse
@prefix : <https://eyereasoner.github.io/ns#>.

:stone :color :black .
:stone :color :white .

{ ?X :color :black .
  ?X :color :white .
} => false.
```

Semantics:

* As soon as the premise is provable, the engine:

  * prints a short message about the fuse being triggered, and
  * exits with **status code 2**.
* This mirrors the “fuse” / inconsistency-detection behavior in EYE.

The `Makefile` treats the non-zero exit code for the `fuse.n3` example as **expected** and still considers the example run successful.

---

## Built-ins (overview)

Built-ins are recognized by expanded IRIs and evaluated during goal proving (backward phase).

A very condensed overview:

### `math:` namespace

Arithmetic on numeric literals (mostly list forms):

* `math:sum`
* `math:product`
* `math:difference`
* `math:quotient`
* `math:exponentiation`

Unary ops:

* `math:negation`
* `math:absoluteValue`

Trigonometry:

* `math:sin`
* `math:cos`
* `math:asin`
* `math:acos`

Comparison:

* `math:greaterThan`
* `math:lessThan`
* `math:notLessThan`
* `math:notGreaterThan`

Dates & durations:

* `math:difference` can take `xsd:date` / `xsd:dateTime` and returns an `xsd:duration`.
* Duration and date values are internally mapped to seconds to allow comparisons.

Integer arithmetic:

* For lists of plain integer literals, `math:sum` and `math:difference` use **arbitrary precision integers** (via `num-bigint`) instead of `f64`.

  * This supports examples like big Fibonacci numbers without overflow or rounding.
  * Mixed/non-integer cases fall back to `f64` as before.

### `log:` namespace

* `log:equalTo`

  * Relational: succeeds iff the subject and object terms can be unified.
  * May bind variables on either side.
* `log:notEqualTo`

  * The exact complement of `log:equalTo`:

    * Succeeds iff there is **no** unifier for subject and object given the current substitution.
    * Does not introduce new bindings; it acts as a constraint.

### `time:` namespace

* `time:localTime` — SWAP-style:

  * `"" time:localTime ?D.` binds `?D` to the current local time as `xsd:dateTime`.

### `list:` namespace

Operations on lists:

* `list:append`

  * Relational, Prolog-style **append over a list of lists**.
  * Subject is a list-of-lists; object is the concatenation of those lists.
  * Works in multiple “directions”, e.g.:

    * `( ((1 2) (3 4)) ) list:append ?L.`
    * `( (?P (3 4)) ) list:append (1 2 3 4).`
    * `( ((1 2) ?S) ) list:append (1 2 3 4).`
  * This enables list sublist encodings like the famous zebra puzzle.
* `list:firstRest`

  * Split or construct a list from `(first rest)` (supports an internal open-tail representation for some inverse cases).
* `list:member`

  * Membership; bidirectional over (effectively) ground lists.
* `list:in`

  * Dual of `list:member`.
* `list:length`

  * Length of a list (integer literal).
* `list:map`

  * Pragmatic “map a builtin over a list” helper:
  * Example:
    `((a b c) math:absoluteValue) list:map (|a| |b| |c|).`
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
  * rule-producing rules
  * built-ins
  * CLI

Dependencies:

* [`chrono`](https://crates.io/crates/chrono) for `time:localTime` and date/duration built-ins.
* [`num-bigint`](https://crates.io/crates/num-bigint) for `math:sum` and `math:difference` built-ins.
* Standard library only otherwise.

---

## Building and running examples

```bash
make
```

This builds the `eyeling` binary and runs the examples in [examples](https://github.com/eyereasoner/eyeling/tree/main/examples)
which should give [examples-output.n3](https://github.com/eyereasoner/eyeling/blob/main/examples-output.n3).

