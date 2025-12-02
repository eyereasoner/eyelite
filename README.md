# eyeling

A minimal [Notation3 (N3)](https://notation3.org/) reasoner in **Python**.

`eyeling` is meant to be **tiny** and **close in spirit to EYE** on a small but practical fragment of N3. It parses a useful subset of N3 (a superset of common Turtle usage) and does forward + backward chaining over Horn-style rules, with a growing set of N3 built-ins. It also prints **small mathematical-English proofs** as N3 comments for each derived triple.

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

- Not a full W3C N3 grammar (edge-case identifiers, path expressions, explicit quantifiers, …)
- Quoted formulas in rules are matched only as **whole formulas**; there is no pattern-matching inside them yet
- No *global* proof tree export yet (but **each derived triple** is printed with a local justification as N3 comments)
- Built-ins are intentionally incomplete: a **small, pragmatic subset** (enough for the included examples and some N3 builtin patterns)

---

## Reasoning model

### Forward + backward chaining

- **Forward chaining to fixpoint** over forward rules (`=>`).
- **Backward chaining** (SLD-style) over backward rules (`<=`) and built-ins.

Forward-rule premises are proved using:

- Ground input facts
- Backward rules
- Built-ins

Then the (ground) conclusion triples are added to the fact set.

The command-line tool prints **only newly derived forward facts**, not the original input facts.

### Per-triple explanations

For every newly derived forward fact, `eyeling` prints:

1. A block of `#`-comments explaining **why that triple holds**, then  
2. The triple itself in N3/Turtle syntax.

Each explanation block includes:

- The **derived triple**.
- The **instantiated premises** (rule body after applying the successful substitution).
- The **schematic forward rule** that fired (with variables).
- The **substitution** on the variables that actually occur in that rule (internal helper variables are filtered out).
- A short English sentence stating that the triple is entailed by the rules and facts.

Shape-wise, the output looks like:

```n3
# ----------------------------------------------------------------------
# Proof for derived triple:
#   :s :p :o .
# It holds because the following instantiated premises are all satisfied:
#   :s :q 42 .
#   42 math:greaterThan 0 .
# via the schematic forward rule:
#   {
#     ?S :q ?N .
#     (?N 0) math:greaterThan true .
#   } => {
#     ?S :p :o .
#   }
# with substitution (on rule variables):
#   ?N = 42
#   ?S = :s
# Therefore the derived triple above is entailed by the rules and facts.
# ----------------------------------------------------------------------
:s :p :o .
```

This is **not** a full EYE-style global proof tree, but a compact per-step justification that’s easy to read next to the output triples.

---

## Rule-producing rules (meta-rules)

`eyeling` understands rules that *produce* other rules, using the `log:implies` / `log:impliedBy` idiom.

Top level:

* A triple of the form

  ```n3
  { P } log:implies { C } .
  ```

  is turned into a forward rule

  ```n3
  { P } => { C } .
  ```

* A triple of the form

  ```n3
  { H } log:impliedBy { B } .
  ```

  is turned into a backward rule

  ```n3
  { H } <= { B } .
  ```

Nested in formulas:

* Inside a formula `{ ... }`, `A => B` is normalized as `A log:implies B`.
* Likewise, `A <= B` becomes `A log:impliedBy B`.

During reasoning:

* Any **derived** triple whose predicate is `log:implies` / `log:impliedBy` and whose subject and object are formulas is also turned into a new live rule (forward or backward).
* The triple itself is kept as a fact and printed in `{ ... } => { ... } .` / `{ ... } <= { ... } .` syntax.

This supports EYE-style meta-programs, such as rules that generate subclass-propagation rules, property rules, etc.

---

## Backward search depth (safety guard)

The backward prover has a simple depth limit (`MAX_BACKWARD_DEPTH`) to protect against infinite or extremely deep recursion. If the limit is hit, that proof path is cut off.

It currently relies on:

* The depth limit, and
* A “visited goals” stack

to avoid trivial loops during backward reasoning.

---

## Blank nodes and quantification

`eyeling` tries to mimic the usual N3 / EYE intuition:

### 1. Blank nodes in facts → normal RDF blanks

Top-level triples like:

```n3
[] :p :o .
[ :p :o ] :q :r .
```

are parsed as normal RDF blank nodes. They have stable IDs like `_:b1`, `_:b2` inside a single run.

### 2. Blank nodes in rule premises → universals

In rule premises (the left side of `=>` / the right side of `<=`):

```n3
{ _:A rdfs:subClassOf ?B .
  ?S a _:A .
} => {
  ?S a ?B .
}.
```

the locally scoped `_:` nodes are treated like **rule-scoped universal variables**:

* `_:A` inside a rule body behaves as if it were written `?A`.
* Occurrences of the same `_:` label inside that rule premise are linked together.

The same applies to property-list syntax:

```n3
{ ?S a [ rdfs:subClassOf ?B ] . } => { ?S a ?B . }.
```

Here the inlined `[ rdfs:subClassOf ?B ]` introduces a body-local “class” that behaves as a universally quantified variable in that rule.

### 3. Blank nodes in rule conclusions → existentials

If a blank node appears **only in the rule head**, it is treated as an existential:

```n3
@prefix : <http://example.org/#> .

:Socrates a :Human.
:Plato   a :Human.

{ ?S a :Human. } => { ?S :is _:B. }.
```

Each time this rule fires, `eyeling` creates a fresh Skolem blank:

```n3
@prefix : <http://example.org/#> .

:Socrates :is _:sk_0 .
:Plato    :is _:sk_1 .
```

Key points:

* Skolem IDs (`_:sk_0`, `_:sk_1`, …) are unique per rule firing.
* Equal facts up to renaming of Skolem IDs are treated as duplicates and are not re-added, to avoid trivial infinite loops.

---

## Inference fuse — `{ ... } => false.`

`eyeling` treats rules whose conclusion is `false` as **hard failures**:

```n3
# inference fuse
@prefix : <http://example.org/#> .

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

The `Makefile` / example scripts treat the non-zero exit code for the `fuse.n3` example as **expected** and still consider the overall example run successful.

---

## Built-ins (overview)

Built-ins are recognized by expanded IRIs and evaluated during goal proving (backward phase).

This is a **condensed** overview of what’s currently implemented. For the exact behavior and corner cases, see the `eval_builtin` function in `eyeling.py`.

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
* Duration and date/dateTime values are internally mapped to seconds to allow comparisons.

Integer arithmetic:

* For lists of plain integer literals, `math:sum` and `math:difference` use Python’s **arbitrary precision integers** instead of floating-point.
* This supports examples like big Fibonacci numbers without overflow or rounding.
* Mixed / non-integer cases fall back to `float` as before.

(If you add more `math:` built-ins, they naturally plug into `list:map`.)

### `log:` namespace

* `log:equalTo`

  * Relational: succeeds iff the subject and object terms can be **unified**.
  * May bind variables on either side.
* `log:notEqualTo`

  * Exact complement of `log:equalTo`.
  * Succeeds iff there is **no** unifier for subject and object given the current substitution.
  * Does not introduce new bindings; acts as a constraint.
* `log:collectAllIn` (pragmatic subset)

  * Subject shape: `( ?V { WHERE } ?List )`.
  * Object is a “scope” term (often a blank node or variable) but is currently treated as “this reasoning run”.
  * Informal semantics:

    * Evaluate the `WHERE` graph pattern in the current reasoning scope.
    * For each solution, collect the value of `?V` into `?List`.
  * This is enough to support patterns like:

    * Dijkstra’s algorithm (collect neighbor queue entries).
    * Counting / aggregating events in a local graph.
* `log:notIncludes` (Scoped Negation As Failure)

  * Shape:

    ```n3
    ?Scope log:notIncludes { ...pattern... } .
    ```

  * Current behavior:

    * Evaluate the quoted `{ pattern }` against the current closure (facts + rules + built-ins).
    * If there is **no** way to prove all triples in `{ pattern }`, the builtin **succeeds** (and introduces no new bindings).
    * If there **is** at least one proof of `{ pattern }`, the builtin fails.

### `time:` namespace

* `time:localTime` — SWAP-style:

  ```n3
  "" time:localTime ?D.
  ```

  binds `?D` to the current local time as `xsd:dateTime`.

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
  * Example:

    ```n3
    (( (1 -2 3) math:absoluteValue) list:map (1 2 3)).
    ```

* `list:notMember`

  * Succeeds iff the element does **not** occur in the list.
  * Used for scoped negation patterns like “not visited yet” in graph algorithms.

* `list:reverse`

  * Reverses a list (useful to flip accumulated paths).

* `list:sort`

  * Sorts a list using a pragmatic comparator, good enough for the examples.
  * In the Dijkstra example, it’s used to sort the priority queue by cost.

These list built-ins are designed to match common patterns from the N3 builtin report, not yet every corner case.

---

## Project layout

The project is deliberately small and self-contained:

* `eyeling.py` — everything in one file:

  * lexer
  * parser & AST
  * unification
  * backward prover
  * forward engine
  * rule-producing rules
  * built-ins
  * explanations / proof comments
  * CLI

Dependencies:

* Python 3 (3.10+ recommended).
* Standard library only (`datetime` for time/date builtins, etc.). No external packages required.

---

## Running and examples

To run `eyeling` on a single N3 file:

```bash
python eyeling.py examples/socrates.n3
```

This reads the input file, runs forward + backward reasoning to a fixpoint, and prints:

* Only the newly derived forward facts, and
* Interleaved proof comments as described above.

The repository includes N3 programs in [`examples`](https://github.com/eyereasoner/eyeling/tree/main/examples). They cover:

* Classic toy reasoning snippets,
* Meta-rules,
* Small numeric / list puzzles (including big Fibonacci),
* A Dijkstra shortest-path program using `list:` and `log:` built-ins,
* And more mathematically flavored examples (e.g., complex numbers).

You can test all the examples with:

```bash
cd examples
./test
```

and get [`output`](https://github.com/eyereasoner/eyeling/tree/main/examples/output)
All derived output is annotated with interleaved mathematical-English proof comments.

