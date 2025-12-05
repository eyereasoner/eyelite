# eyeling

A minimal [Notation3 (N3)](https://notation3.org/) reasoner in **JavaScript**.

`eyeling` is:

- a **single self-contained file** (`eyeling.js`, no external deps),
- intentionally **tiny** and **close in spirit to EYE**,
- operating on a practical fragment of N3 (a superset of common Turtle usage),
- and capable of **forward + backward chaining** over Horn-style rules
  with a pragmatic subset of N3 built-ins.

For every derived triple, it also prints a compact, mathematical-English proof
as N3 comments.

---

## Quick start

### Requirements

- A reasonably recent Node.js (tested on current Node; anything with
  `BigInt` support should be fine).

### Running a single file

From the repo root:

```bash
# Option 1: use the shebang (on Unix-like systems)
./eyeling.js examples/socrates.n3

# Option 2: explicit node
node eyeling.js examples/socrates.n3
```

`eyeling` will:

* parse the input,
* run forward + backward reasoning to a fixpoint, and
* print only **newly derived forward facts**, each preceded by a proof block.

The repository includes `examples/*.n3` and their corresponding
`examples/output/*` so you can see the expected behavior.

To run all examples at once:

```bash
cd examples
./test
```

This runs `eyeling.js` over each example and compares against
the golden outputs in `examples/output`.

---

## What kind of output do I get?

For each newly derived triple, `eyeling` prints:

1. A block of `#`-comments explaining **why that triple holds**, and then
2. The triple itself in N3/Turtle syntax.

Shape-wise, the output looks like:

```n3
# ----------------------------------------------------------------------
# Proof for derived triple:
# :s :p :o .
# It holds because the following instantiated premises are all satisfied:
# :s :q 42 .
# 42 math:greaterThan 0 .
# via the schematic forward rule:
# {
# ?S :q ?N .
# (?N 0) math:greaterThan true .
# } => {
# ?S :p :o .
# } .
# with substitution (on rule variables):
# ?N = 42
# ?S = :s
# Therefore the derived triple above is entailed by the rules and facts.
# ----------------------------------------------------------------------

:s :p :o .
```

This is **not** a full EYE-style global proof tree, but a compact per-step
justification that’s easy to read next to the derived triples.

---

## Features

### Parsing — practical N3 subset

Supported:

* `@prefix` and `@base`
* Triples with `;` / `,` predicate–object lists
* Variables `?x`
* Blank nodes:

  * Anonymous `[]`
  * Property lists `[ :p :o; :q :r ]`
* Collections `( ... )`
* Quoted formulas `{ ... }`
* Implications:

  * Forward rules `{ P } => { C } .`
  * Backward rules `{ C } <= { P } .`
* Datatyped literals with `^^` (e.g. `"1944-08-21"^^xsd:date`)
* `#` line comments

Non-goals / current limits:

* Not a full W3C N3 grammar (edge cases for identifiers, path expressions,
  explicit quantifiers, …)
* Quoted formulas in rules are matched only as **whole formulas**; there is
  no pattern-matching *inside* them yet
* No *global* proof tree export (only per-triple justifications)
* Built-ins are intentionally incomplete: a **small, pragmatic subset**
  (enough for the included examples and some common N3 builtin patterns)

---

## Reasoning model

### Forward + backward chaining

* **Forward chaining to fixpoint** over forward rules (`=>`).
* **Backward chaining** (SLD-style) over backward rules (`<=`) and built-ins.

Forward-rule premises are proved using:

* Ground input facts
* Backward rules
* Built-ins

When a forward rule fires, its (ground) conclusion triples are added to the
fact set. The CLI prints **only newly derived forward facts**, *not* the
original input facts.

### Rule-producing rules (meta-rules)

`eyeling` understands rules that *produce* other rules, using the
`log:implies` / `log:impliedBy` idiom.

Top level:

* A triple

  ```n3
  { P } log:implies { C } .
  ```

  becomes a forward rule

  ```n3
  { P } => { C } .
  ```

* A triple

  ```n3
  { H } log:impliedBy { B } .
  ```

  becomes a backward rule

  ```n3
  { H } <= { B } .
  ```

Nested in formulas:

* Inside a formula `{ ... }`, `A => B` is normalized as `A log:implies B`.
* Likewise, `A <= B` becomes `A log:impliedBy B`.

During reasoning:

* Any **derived** triple whose predicate is `log:implies` / `log:impliedBy`
  and whose subject and object are formulas is turned into a new live
  forward/backward rule.
* The triple itself is kept as a fact and printed in `{ ... } => { ... } .`
  / `{ ... } <= { ... } .` syntax.

This supports EYE-style meta-programs, such as rules that generate
subclass-propagation rules, property rules, etc.

### Backward search depth (safety guard)

The backward prover has a configurable depth limit (`MAX_BACKWARD_DEPTH`) to
protect against infinite or extremely deep recursion. If the limit is hit,
that proof path is cut off.

The implementation currently relies on:

* This depth limit, and
* A “visited goals” stack to avoid trivial loops during backward reasoning.

---

## Blank nodes and quantification

`eyeling` tries to mirror the usual N3 / EYE intuition:

### 1. Blank nodes in facts → normal RDF blanks

Top-level triples like:

```n3
[] :p :o .
[ :p :o ] :q :r .
```

are parsed as normal RDF blank nodes. They get stable IDs such as `_:b1`,
`_:b2` inside a single run.

### 2. Blank nodes in rule premises → universals

In rule premises (the left side of `=>` / the right side of `<=`):

```n3
{
  _:A rdfs:subClassOf ?B .
  ?S a _:A .
} => {
  ?S a ?B .
}.
```

the locally scoped `_:` nodes are treated like **rule-scoped universal
variables**:

* `_:A` inside a rule body behaves as if it were written `?A`.
* All occurrences of the same `_:` label inside that rule premise are
  linked together.

The same applies to property-list syntax:

```n3
{
  ?S a [ rdfs:subClassOf ?B ] .
} => {
  ?S a ?B .
}.
```

Here the inlined `[ rdfs:subClassOf ?B ]` introduces a body-local “class”
that behaves as a universally quantified variable in that rule.

### 3. Blank nodes in rule conclusions → existentials

If a blank node appears **only in the rule head**, it is treated as an
existential:

```n3
@prefix : <http://example.org/> .

:Socrates a :Human.
:Plato    a :Human.

{ ?S a :Human. } => { ?S :is _:B. }.
```

Each time this rule fires, `eyeling` creates a fresh Skolem blank:

```n3
@prefix : <http://example.org/> .

:Socrates :is _:sk_0 .
:Plato    :is _:sk_1 .
```

Key points:

* Skolem IDs (`_:sk_0`, `_:sk_1`, …) are unique per rule firing.
* Equal facts up to renaming of Skolem IDs are treated as duplicates and are
  not re-added, to avoid trivial infinite loops.

---

## Inference fuse — `{ ... } => false.`

`eyeling` treats rules whose conclusion is `false` as **hard failures**:

```n3
# inference fuse
@prefix : <http://example.org/> .

:stone :color :black .
:stone :color :white .

{ ?X :color :black .
  ?X :color :white . } => false.
```

Semantics:

* As soon as the premise is provable, the engine:

  * prints a short message about the fuse being triggered, and
  * exits with **status code 2**.
* This mirrors the “fuse” / inconsistency-detection behavior in EYE.

The `examples/test` script treats this non-zero exit code for the `fuse.n3`
example as **expected**, and still considers the overall example run
successful.

---

## Built-ins (overview)

Built-ins are recognized by expanded IRIs and evaluated during **backward**
goal proving.

This is a **condensed** overview of what’s currently implemented. For exact
behavior and corner cases, see the `evalBuiltin` function in `eyeling.js`.

### `math:` namespace

Arithmetic on numeric literals:

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
* `math:equalTo`
* `math:notEqualTo`

Other:

* `math:fibonacci`

  `math:fibonacci` is BigInt-aware and uses 0-based indexing:
  Integer inputs are treated as unbounded BigInts; outputs are exact
  (also as integer literals).

Dates & durations:

* `math:difference` can take `xsd:date` / `xsd:dateTime` and returns an
  `xsd:duration`.
* Duration and date/dateTime values are internally mapped to seconds to
  allow comparisons.

### `log:` namespace

* `log:equalTo`

  * Relational: succeeds iff the subject and object terms can be **unified**.
  * May bind variables on either side.

* `log:notEqualTo`

  * Exact complement of `log:equalTo`.
  * Succeeds iff there is **no** unifier for subject and object given the
    current substitution.
  * Does not introduce new bindings; acts as a constraint.

* `log:implies` / `log:impliedBy` (rule introspection)
  * These do **intensional introspection** over the current rulebase, not over ordinary data triples.
  * `log:implies` — forward rules:
    * Shape: `?P log:implies ?C .`
    * For each forward rule currently known to `eyeling`:
      ```n3
      { P0 } => { C0 } .
      ```
      this goal succeeds once, unifying:
      * `?P` with `{ P0 }` and
      * `?C` with `{ C0 }`
      as quoted formulas.
  * `log:impliedBy` — backward rules:
    * Shape: `?H log:impliedBy ?B .`
    * For each backward rule:
      ```n3
      { H0 } <= { B0 } .
      ```
      this goal succeeds once, unifying:
      * `?H` with `{ H0 }` and
      * `?B` with `{ B0 }`
      as quoted formulas.
  * The rulebase seen by these built-ins includes:
    * rules written directly as `{ ... } => { ... } .` / `{ ... } <= { ... } .`, and
    * rules **generated at runtime** via the `log:implies` / `log:impliedBy` meta-rule idiom described above.
  * Implementation detail: each introspected rule is **standardized apart** before being exposed, so its internal variables show up with fresh names like `?X__0`. This avoids cyclic substitutions (occurs-check issues) even when a rule introspects *itself*. As elsewhere in `eyeling`, quoted formulas are matched as **whole formulas**; there is no pattern-matching *inside* them yet.

* `log:collectAllIn` (pragmatic subset)

  * Subject shape: `( ?V { WHERE } ?List )`.
  * Object is a “scope” term (often a blank node or variable) but is
    currently treated as “this reasoning run”.
  * Informal semantics:

    * Evaluate the `{ WHERE }` pattern in the current reasoning scope.
    * For each solution, collect the value of `?V` into `?List`.

  This is enough to support patterns like:

  * Dijkstra-style neighbor queue collection
  * Counting / aggregating events in a local graph

* `log:notIncludes` (Scoped Negation As Failure)

  * Shape:

    ```n3
    ?Scope log:notIncludes { ...pattern... } .
    ```

  * Behavior:

    * Evaluate the quoted `{ pattern }` against the current closure
      (facts + rules + built-ins).
    * If there is **no** way to prove all triples in `{ pattern }`,
      the builtin **succeeds** (and introduces no new bindings).
    * If there **is** at least one proof of `{ pattern }`, the builtin fails.

### `time:` namespace

* `time:localTime` — SWAP-style:

  ```n3
  "" time:localTime ?D.
  ```

  Binds `?D` to the current local time as `xsd:dateTime`.

### `list:` namespace

Operations on lists:

* `list:append`

  * Relational, Prolog-style **append over a list of lists**.
  * Subject is a list-of-lists; object is the concatenation of those lists.
  * Works in multiple “directions”, e.g.:

    ```n3
    ((1 2) (3 4)) list:append ?L.
    (?P (3 4))    list:append (1 2 3 4).
    ((1 2) ?S)    list:append (1 2 3 4).
    ```

* `list:firstRest`

  * Split or construct a list from `(first rest)`.
  * Supports an internal open-tail representation for some inverse cases.

* `list:member`

  * Membership; bidirectional over (effectively) ground lists.

* `list:in`

  * Dual of `list:member` (element on subject side).

* `list:length`

  * Length of a list (integer literal).

* `list:map` (pragmatic subset)

  * Shape: `( (inputList) predicateIRI ) list:map outputList`.
  * Only works when:

    * the predicate is itself a builtin, and
    * the input list is ground.

  Example:

  ```n3
  (( (1 -2 3) math:absoluteValue) list:map (1 2 3)).
  ```

* `list:notMember`

  * Succeeds iff the element does **not** occur in the list.
  * Used for scoped negation patterns like “not visited yet” in graph
    algorithms.

* `list:reverse`

  * Reverses a list (useful to flip accumulated paths).

* `list:sort`

  * Sorts a list using a pragmatic comparator, good enough for the examples.
  * In the Dijkstra example, it’s used to sort the priority queue by cost.

These list built-ins aim to match common patterns from the N3 builtin report,
not every corner case.

---

## Project layout

The project is deliberately small and self-contained:

* `eyeling.js`:

  * lexer
  * parser & AST
  * unification
  * backward prover
  * forward engine
  * rule-producing rules
  * built-ins (math, log, list, time, including `math:fibonacci`)
  * explanations / proof comments
  * CLI

The `examples/` directory contains small N3 programs that exercise most of
this functionality (including big Fibonacci, graphs, and more
mathematically flavored snippets).

