# eyeling

A minimal [Notation3 (N3)](https://notation3.org/) reasoner in **JavaScript**.

`eyeling` is:

- a **single self-contained file** (`eyeling.js`, no external deps),
- intentionally **tiny** and **close in spirit to EYE**,
- operating on a practical fragment of N3 (a superset of common Turtle usage),
- and capable of **forward + backward chaining** over Horn-style rules with a pragmatic subset of N3 built-ins.

For every derived triple, it also prints a compact, mathematical-English proof as N3 comments.

---

## Quick start

### Requirements

- A reasonably recent Node.js (tested on current Node; anything with `BigInt` support should be fine).

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

The repository includes `examples/*.n3` and their corresponding `examples/output/*` so you can see the expected behavior.

To see the version (from `package.json`):

```bash
node eyeling.js --version
# or
node eyeling.js -v
```

### Running all examples

To run all examples at once:

```bash
cd examples
./test
```

This runs `eyeling.js` over each example and compares against the golden outputs in `examples/output`.

---

## What kind of output do I get?

For each newly derived triple, `eyeling` prints:

1. A block of `#`-comments explaining **why that triple holds**, and then
2. The triple itself in N3/Turtle syntax.

Shape-wise, the output looks like:

```n3
@prefix : <http://example.org/socrates#> .

# ----------------------------------------------------------------------
# Proof for derived triple:
#   :Socrates a :Mortal .
#
# It holds because the following instance of the rule body is provable:
#   :Socrates a :Human .
#   :Human rdfs:subClassOf :Mortal .
# via the schematic forward rule:
#   {
#     ?S a ?A .
#     ?A rdfs:subClassOf ?B .
#   } => {
#     ?S a ?B .
#   } .
#
# with substitution (on rule variables):
#   ?A = :Human
#   ?B = :Mortal
#   ?S = :Socrates
#
# Therefore the derived triple above is entailed by the rules and facts.
# ----------------------------------------------------------------------
:Socrates a :Mortal .
```

This is **not** a full EYE-style global proof tree, but a compact per-step justification that’s easy to read next to the derived triples.

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

* Not a full W3C N3 grammar (edge cases for identifiers, path expressions, explicit quantifiers, …)
* Quoted formulas in rules are matched only as **whole formulas**; there is no pattern-matching *inside* them yet
* No *global* proof tree export (only per-triple justifications)
* Built-ins are intentionally incomplete: a **small, pragmatic subset** (enough for the included examples and some common N3 builtin patterns)

---

## Reasoning model

### Forward + backward chaining

* **Forward chaining to fixpoint** over forward rules (`=>`).
* **Backward chaining** (SLD-style) over backward rules (`<=`) and built-ins.

Forward-rule premises are proved using:

* Ground input facts
* Backward rules
* Built-ins

When a forward rule fires, its (ground) conclusion triples are added to the fact set. The CLI prints **only newly derived forward facts**, *not* the original input facts.

### Rule-producing rules (meta-rules)

`eyeling` understands rules that *produce* other rules, using the `log:implies` / `log:impliedBy` idiom.

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

* Any **derived** triple whose predicate is `log:implies` / `log:impliedBy` and whose subject and object are formulas is turned into a new live forward/backward rule.
* The triple itself is kept as a fact and printed in `{ ... } => { ... } .` / `{ ... } <= { ... } .` syntax.

This supports EYE-style meta-programs, such as rules that generate subclass-propagation rules, property rules, etc.

### Backward search depth (safety guard)

The backward prover has a configurable depth limit (`MAX_BACKWARD_DEPTH`) to protect against infinite or extremely deep recursion. If the limit is hit, that proof path is cut off.

The implementation currently relies on:

* This depth limit, and
* A “visited goals” stack to avoid trivial loops during backward reasoning.

### Constraint-style built-ins and goal ordering (forward rules)

Some built-ins behave as **pure tests**: they never introduce new variable bindings, they only succeed or fail. Examples:

* Numeric comparisons in `math:`:
  * `math:greaterThan`
  * `math:lessThan`
  * `math:notLessThan`
  * `math:notGreaterThan`
  * `math:equalTo`
  * `math:notEqualTo`

* List membership test in `list:`:
  * `list:notMember`

* Pure tests in `log:`:
  * `log:forAllIn`
  * `log:notEqualTo`
  * `log:notIncludes`

* String comparison / membership / regex tests in `string:`:
  * `string:contains`
  * `string:containsIgnoringCase`
  * `string:endsWith`
  * `string:startsWith`
  * `string:equalIgnoringCase`
  * `string:notEqualIgnoringCase`
  * `string:greaterThan`
  * `string:lessThan`
  * `string:notGreaterThan`
  * `string:notLessThan`
  * `string:matches`
  * `string:notMatches`

For **forward rules** (`=>`), `eyeling` automatically **delays** such constraint-style built-ins to the **end of the rule premise**:

* Non-constraint goals (which can bind variables) are tried first.
* Constraint-style built-ins are checked afterwards, once more bindings are in place.
* The relative order of the **non-constraint** goals is preserved.

This is similar in spirit to Prolog’s `when/2`, but hard-wired for known constraint predicates.

**Backward rules** (`<=`) are **not reordered**: they are executed strictly in the order you write them.

This means that in a forward rule you can safely write:

```n3
@prefix : <https://eyereasoner.github.io/ns#> .
@prefix log: <http://www.w3.org/2000/10/swap/log#> .

{
  ?O1 log:notEqualTo ?O2 .

  ?W1 :has (?O1 ?N1) .
  ?W2 :has (?O2 ?N2) .
}
=>
{
  :test :is true .
} .
```

Even though the `log:notEqualTo` appears syntactically first, `eyeling` will internally prove the `:has` goals first (to bind `?O1` / `?O2`) and only then check the inequality.

---

## Blank nodes and quantification

`eyeling` tries to mirror the usual N3 / EYE intuition:

### 1. Blank nodes in facts → normal RDF blanks

Top-level triples like:

```n3
[] :p :o .
[ :p :o ] :q :r .
```

are parsed as normal RDF blank nodes. They get stable IDs such as `_:b1`, `_:b2` inside a single run.

### 2. Blank nodes in rule premises → universals

In rule premises (the left side of `=>` / the right side of `<=`):

```n3
{
  _:A rdfs:subClassOf ?B .
  ?S  a              _:A .
} => {
  ?S a ?B .
}.
```

the locally scoped `_:` nodes are treated like **rule-scoped universal variables**:

* `_:A` inside a rule body behaves as if it were written `?A`.
* All occurrences of the same `_:` label inside that rule premise are linked together.

The same applies to property-list syntax:

```n3
{
  ?S a [ rdfs:subClassOf ?B ] .
} => {
  ?S a ?B .
}.
```

Here the inlined `[ rdfs:subClassOf ?B ]` introduces a body-local “class” that behaves as a universally quantified variable in that rule.

### 3. Blank nodes in rule conclusions → existentials

If a blank node appears **only in the rule head**, it is treated as an existential:

```n3
@prefix : <http://example.org/> .

:Socrates a :Human .
:Plato    a :Human .

{
  ?S a :Human .
} => {
  ?S :is _:B .
}.
```

Each time this rule fires, `eyeling` creates a fresh Skolem blank:

```n3
@prefix : <http://example.org/> .

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
@prefix : <http://example.org/> .

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

The `examples/test` script treats this non-zero exit code for the `fuse.n3` example as **expected**, and still considers the overall example run successful.

---

## Built-ins (overview)

`eyeling` implements a pragmatic subset of the core N3 builtin vocabularies, roughly following the “Notation3 Builtin Functions” report (sections 4.2–4.6 for math, time, list, log, and string).  

#### Quick map (by namespace)

| Namespace | Role / topic                                        | N3 Builtins section | Notes in `eyeling` (implemented built-ins) |
|-----------|-----------------------------------------------------|---------------------|--------------------------------------------|
| `crypto:` | Cryptographic hashes                                | §4.1 crypto         | Implements: `crypto:sha` (SHA-1, as in the N3 Builtins report), plus EYE-style `crypto:md5`, `crypto:sha256`, `crypto:sha512`. All operate on the lexical form of the subject literal (as UTF-8) and return the lowercase hex digest as a plain string literal. |
| `math:`   | Arithmetic, trig, comparisons, misc.                | §4.2 math           | Implements: `math:greaterThan`, `math:lessThan`, `math:notLessThan`, `math:notGreaterThan`, `math:equalTo`, `math:notEqualTo`, `math:sum`, `math:product`, `math:difference`, `math:quotient`, `math:exponentiation`, `math:negation`, `math:absoluteValue`, `math:cos`, `math:sin`, `math:acos`, `math:asin`, `math:atan`, `math:cosh`, `math:sinh`, `math:degrees`, `math:remainder`, `math:rounded`, `math:tan`, `math:tanh`, `math:fibonacci`. |
| `time:`   | Time and dates                                      | §4.3 time           | Implements: `time:day`, `time:month`, `time:year`, `time:minute`, `time:second`, `time:timeZone`, `time:localTime`. |
| `list:`   | List/collection utilities                           | §4.4 list           | Implements: `list:append`, `list:firstRest`, `list:first`, `list:last`, `list:in`, `list:member`, `list:memberAt`, `list:iterate`, `list:length`, `list:remove`, `list:notMember`, `list:reverse`, `list:sort`, `list:map`. |
| `log:`    | Logical / meta reasoning, SNAF, rule introspection  | §4.5 log           | Implements: `log:equalTo`, `log:notEqualTo`, `log:implies`, `log:impliedBy`, `log:notIncludes`, `log:collectAllIn`, `log:forAllIn`, `log:uri`, `log:skolem`. |
| `string:` | String processing and regex-like operations         | §4.6 string         | Implements: `string:concatenation`, `string:contains`, `string:containsIgnoringCase`, `string:endsWith`, `string:equalIgnoringCase`, `string:format` (subset: `%s`, `%%`), `string:greaterThan`, `string:lessThan`, `string:matches`, `string:notEqualIgnoringCase`, `string:notGreaterThan`, `string:notLessThan`, `string:notMatches`, `string:replace`, `string:scrape`, `string:startsWith`. |

Built-ins are recognized by expanded IRIs and evaluated during **backward** goal proving. This is a **condensed** overview of what’s currently implemented. For exact behavior and corner cases, see the `evalBuiltin` function in `eyeling.js`.

### `crypto:` namespace

Cryptographic hashes using the SWAP `crypto:` vocabulary (and aligned with section 4.1 of the Notation3 Builtin Functions report).  
All `crypto:` builtins in `eyeling` are **functional**: the subject is a literal whose lexical form is hashed as UTF-8, and the object is the lowercase hexadecimal digest as a plain string literal.

Implemented built-ins:

* `crypto:sha`  
  SHA-1 hash of the subject string (the one specified in the N3 Builtins report).  
  Example:  
  ```n3
  "hello world" crypto:sha ?Digest .

derives `?Digest = "2aae6c35c94fcfb415dbe95f408b9ce91ee846ed"`.

* `crypto:md5`
  MD5 hash of the subject string, EYE-style extension.

* `crypto:sha256`
  SHA-256 hash of the subject string.

* `crypto:sha512`
  SHA-512 hash of the subject string.

These are thin wrappers around Node’s `crypto.createHash(alg).update(lexicalForm, "utf8").digest("hex")`, so behavior should match EYE on typical use cases.

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

Trigonometry & angles:

* `math:sin`, `math:cos`  
  Standard sine/cosine (argument in radians).

* `math:asin`, `math:acos`, `math:atan`  
  Inverse trig functions (result in radians).

* `math:cosh`, `math:sinh`  
  Hyperbolic cosine/sine. Implemented via `Math.cosh` / `Math.sinh` when the host JS provides them (otherwise the builtin simply fails).

* `math:tan`, `math:tanh`  
  Tangent / hyperbolic tangent (again via the native `Math.*` functions where available).

Comparison (pure tests; no new bindings):

* `math:greaterThan`
* `math:lessThan`
* `math:notLessThan`
* `math:notGreaterThan`
* `math:equalTo`
* `math:notEqualTo`

These comparisons are treated as **constraints** for goal ordering in forward rules (see above): they only succeed/fail given the current bindings.

Other numeric helpers:

* `math:degrees`  
  Convert radians to degrees. Subject is an angle in radians; object is the corresponding angle in degrees.

* `math:remainder`  
  Remainder of integer division.  
  Shape: `( $Dividend $Divisor ) math:remainder $Remainder`.  
  Implemented using JavaScript’s `%` operator; fails if the divisor is zero or any operand is non-numeric.

* `math:rounded`  
  Round to nearest integer (JavaScript `Math.round` semantics).  
  Shape: `$In math:rounded $Out`.

* `math:fibonacci`  
  BigInt-aware Fibonacci sequence.

`math:fibonacci` is BigInt-aware and uses **0-based** indexing:

* Integer inputs are treated as unbounded BigInts.
* Outputs are exact (also as integer literals).

Dates & durations:

* `math:difference` can take `xsd:date` / `xsd:dateTime` and returns an `xsd:duration`.
* Duration and date/dateTime values are internally mapped to seconds to allow comparisons.

### `time:` namespace

Helpers for working with dates and dateTimes, loosely following section 4.3 of the Notation3 Builtins report. All of these operate on the lexical form of the subject literal and return `xsd:integer` results where applicable.

Extraction built-ins (subject is an `xsd:date` or `xsd:dateTime` literal):

* `time:day`  
  True iff the object is the (1–31) day-of-month of the date/datetime subject.

* `time:month`  
  True iff the object is the (1–12) month number of the subject.

* `time:year`  
  True iff the object is the year of the subject.

* `time:minute`  
  True iff the object is the minute field (0–59) of the `xsd:dateTime` subject, interpreted in UTC.

* `time:second`  
  True iff the object is the second field (0–59) of the `xsd:dateTime` subject, interpreted in UTC.

* `time:timeZone`  
  True iff the object is the time zone offset in **minutes east of UTC** encoded in the `xsd:dateTime` subject.  
  Example: `"2025-01-01T00:00:00+02:00"^^xsd:dateTime` ⇒ `120`.

Current local time:

* `time:localTime` — SWAP-style:

  ```n3
  "" time:localTime ?D.
  ```

  Binds `?D` to the current local time as `xsd:dateTime`.

### `list:` namespace

Operations on lists, roughly following section 4.4 of the Notation3 builtin report, plus a few pragmatic extras.

Construction and reshaping:

* `list:append` (4.4.1)  
  Relational, Prolog-style append over a **list of lists**.  
  Subject is a list of lists; object is the concatenation of those lists. Works in multiple “directions”, e.g.
  ```n3
  ((1 2) (3 4)) list:append ?L .
  (?P (3 4))    list:append (1 2 3 4) .
  ((1 2) ?S)    list:append (1 2 3 4) .

* `list:firstRest`
  Split or construct a list from `( first rest )`.
  Used internally to support some inverse modes.

* `list:first` (4.4.2) / `list:last` (4.4.5)
  First and last element of a list.

* `list:remove` (4.4.9)
  `( List Item ) list:remove OutList` removes **all** occurrences of `Item` from `List`.

Membership and indexing:

* `list:member` (4.4.7)
  Membership; bidirectional over (effectively) ground lists.

* `list:in` (4.4.3)
  Dual of `list:member` with the element on the subject side.

* `list:notMember`
  Succeeds iff the element does **not** occur in the list. Useful for patterns like “not visited yet” in graph algorithms.

* `list:length` (4.4.6)
  Length of a list, returned as an integer literal.

* `list:memberAt` (4.4.8)
  `((List Index) list:memberAt Elem)` relates a list element to its **0-based** index.

* `list:iterate` (4.4.4)
  Iterates over a list as `( index value )` pairs. Example shape:

  ```n3
  ("dog" "penguin" "cat") list:iterate (?I "cat") .
  ```

  This will succeed for `?I = 2`.

Ordering and mapping:

* `list:reverse`
  Reverse the order of a list.

* `list:sort`
  Sort a list with a pragmatic comparator; good enough for the bundled examples (e.g., Dijkstra priority queues).

* `list:map` (pragmatic subset)
  Shape: `( (InputList) PredicateIRI ) list:map OutputList`.
  Currently only supports cases where the predicate is itself a builtin and the input list is ground, e.g.

  ```n3
  (( (1 -2 3) math:absoluteValue) list:map (1 2 3)) .
  ```

These list built-ins aim to mirror the common cases from the N3 builtin report. They’re not a complete re-implementation of every mode and corner case, but they should match EYE on the typical patterns used in the examples.

### `log:` namespace

* `log:equalTo`

  * Relational: succeeds iff the subject and object terms can be **unified**.
  * May bind variables on either side.

* `log:notEqualTo`

  * Exact complement of `log:equalTo`.
  * Succeeds iff there is **no** unifier for subject and object given the current substitution.
  * Does **not** introduce new bindings; acts as a **constraint** and is delayed in forward-rule premises.

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
      * `?C` with `{ C0 }` as quoted formulas.

  * `log:impliedBy` — backward rules:

    * Shape: `?H log:impliedBy ?B .`
    * For each backward rule:

      ```n3
      { H0 } <= { B0 } .
      ```

      this goal succeeds once, unifying:

      * `?H` with `{ H0 }` and
      * `?B` with `{ B0 }` as quoted formulas.

  * The rulebase seen by these built-ins includes:

    * rules written directly as `{ ... } => { ... } .` / `{ ... } <= { ... } .`, and
    * rules **generated at runtime** via the `log:implies` / `log:impliedBy` meta-rule idiom described above.

  * Implementation detail: each introspected rule is **standardized apart** before being exposed, so its internal variables show up with fresh names like `?X__0`. This avoids cyclic substitutions (occurs-check issues) even when a rule introspects *itself*.

  * As elsewhere in `eyeling`, quoted formulas are matched as **whole formulas**; there is no pattern-matching *inside* them yet.

* `log:collectAllIn` (pragmatic subset)

  * Subject shape: `( ?V { WHERE } ?List )`.
  * Object is a “scope” term (often a blank node or variable) but is currently treated as “this reasoning run”.
  * Informal semantics:

    * Evaluate the `{ WHERE }` pattern in the current reasoning scope.
    * For each solution, collect the value of `?V` into `?List`.
  * This is enough to support patterns like:

    * Dijkstra-style neighbor queue collection
    * Counting / aggregating events in a local graph

* `log:notIncludes` (Scoped Negation As Failure)

  * Shape:

    ```n3
    ?Scope log:notIncludes { ...pattern... } .
    ```

  * Behavior:

    * Evaluate the quoted `{ pattern }` against the current closure (facts + rules + built-ins).
    * If there is **no** way to prove all triples in `{ pattern }`, the builtin **succeeds** (and introduces no new bindings).
    * If there **is** at least one proof of `{ pattern }`, the builtin fails.

  * This is a pure test and is also treated as a **constraint** for goal ordering in forward rules.

* `log:forAllIn` (universal condition over a where/then pair)

  * Subject shape (current `eyeling` implementation):

    ```n3
    ( { WHERE } { THEN } ) log:forAllIn ?Scope .
    ```

    `?Scope` is currently just a placeholder; the scope is “this reasoning run”.

  * Semantics (as implemented):

    1. Evaluate `{ WHERE }` against the current closure (facts + rules + builtins), collecting all substitutions that make it true.
    2. For **every** such substitution, check that `{ THEN }` also holds under that substitution.
    3. If there is a substitution that satisfies `{ WHERE }` but **not** `{ THEN }`, the builtin fails.
    4. If there are no matches for `{ WHERE }` at all, the builtin is **vacuously true**.

  * It does **not** introduce new bindings; it’s a pure test and is treated as a **constraint** in forward-rule bodies (run after other goals have bound the variables).

* `log:uri` (IRI ↔ string literal bridge)

  * Direction 1 (IRI → string):

    ```n3
    <https://www.w3.org/> log:uri ?S .
    ```

    Succeeds with `?S` bound to `"https://www.w3.org/"`.

  * Direction 2 (string → IRI):

    ```n3
    ?R log:uri "https://www.w3.org/" .
    ```

    Succeeds with `?R` bound to `<https://www.w3.org/>`.

  * If both sides are ground, it just checks they match. If neither side is sufficiently instantiated (both variables, or wrong types), the builtin fails rather than enumerating IRIs.

* `log:skolem` (Skolem IRI generator)

  * Shape:

    ```n3
    ?Term log:skolem ?Sk .
    ```

  * Subject must be **ground** (often a list, but any ground term is allowed).

  * Within one eyeling run:

    * For each distinct subject, `log:skolem` produces a fresh Skolem IRI of the form:

      ```n3
      <urn:eyeling:skolem:UUID>   # e.g., urn:eyeling:skolem:5c0b89f4-6e0d-4f04-8b8a-5fba5a42b807
      ```

    * Repeated calls with the **same** subject produce the **same** IRI (via an internal cache).

  * This builtin **does** introduce bindings (it generates the Skolem IRI), so it is *not* a constraint; it behaves more like a function.

### `string:` namespace

String built-ins following section 4.6 of the Notation3 builtin report (2023-07-03).  
They operate on literals; the lexical form is used as a JavaScript string, and the datatype is ignored.

Core operators:

* `string:concatenation` (4.6.1)  
  Build a string by concatenating a list of input strings.

* `string:contains` / `string:containsIgnoringCase` (4.6.2, 4.6.3)  
  Succeeds iff the subject string contains the object string (case-sensitive / case-insensitive).

* `string:endsWith` / `string:startsWith` (4.6.4, 4.6.16)  
  Succeeds iff the subject ends with / starts with the object.

* `string:equalIgnoringCase` / `string:notEqualIgnoringCase` (4.6.5, 4.6.10)  
  Case-insensitive equality and its negation.

* `string:greaterThan` / `string:lessThan` (4.6.7, 4.6.8)  
  Compare strings using JavaScript’s lexicographic order (Unicode code units).

* `string:notGreaterThan` / `string:notLessThan` (4.6.11, 4.6.12)  
  The ≤ / ≥ counterparts of the comparison built-ins.

Formatting and regex-style operations:

* `string:format` (4.6.6)  
  Pragmatic subset: only `%s` and `%%` are supported. Anything else causes the builtin to fail.  
  Example shape:  
  ```n3
  ("%s://%s/%s" "https" "w3c.github.io" "N3/spec/")
      string:format ?Out .

* `string:matches` / `string:notMatches` (4.6.9, 4.6.13)
  Regular-expression match and its negation. Patterns are interpreted as JavaScript `RegExp` source.

* `string:replace` (4.6.14)
  Global regex replace: subject is `( data pattern replacement )`; object is the result string.
  Implemented via `new RegExp(pattern, "g")` in JavaScript.

* `string:scrape` (4.6.15)
  Regex “extract”: subject is `( data pattern )`; object is the first capturing group of the first match.

All of the comparison / membership / regex-style string built-ins —

`string:contains`, `string:containsIgnoringCase`, `string:endsWith`, `string:startsWith`,  
`string:equalIgnoringCase`, `string:notEqualIgnoringCase`,  
`string:greaterThan`, `string:lessThan`, `string:notGreaterThan`, `string:notLessThan`,  
`string:matches`, `string:notMatches` —

are **pure tests**: they introduce no new bindings and only succeed or fail. In forward rules they are treated as **constraint-style built-ins** and delayed to the end of the rule body (see “Constraint-style built-ins and goal ordering” above).

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
  * constraint-style builtin detection and goal reordering for forward rules
  * explanations / proof comments
  * CLI

The `examples/` directory contains small N3 programs that exercise most of this functionality (including big Fibonacci, graphs, and more mathematically flavored snippets).

