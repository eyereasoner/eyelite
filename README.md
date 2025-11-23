# eyelite

A small Notation3 (N3) parser and lightweight reasoner in Rust.

`eyelite` aims to be tiny, hackable, and useful for experiments. It parses a practical subset of N3 (a superset of Turtle) and performs forward- and backward-chaining over simple Horn-style rules, with a growing set of N3 built-ins.

---

## Features

### Parsing (practical subset of N3)

Supported:

- `@prefix` / `@base` directives
- Triples with `;` and `,` predicate/object lists
- Variables `?x`
- Blank nodes `[]` (anonymous bnodes)
- Collections `(...)`
- Quoted formulas `{ ... }`
- Implications:
  - forward rules `{P} => {C}.`
  - backward rules `{C} <= {P}.`
- Datatyped literals using `^^` (e.g., `"1944-08-21"^^xsd:date`)
- Comments starting with `#`

Non-goals / limitations (for now):

- The full W3C N3 grammar is larger than what we implement (PN_* edge cases, property lists, paths, quantifiers, etc.).
- Quoted-formula **pattern matching** in rules is not implemented (formulas behave like opaque terms unless fully grounded).
- No proof objects.
- Builtins are intentionally incomplete.

---

## Reasoning

- **Forward chaining** to fixpoint over Horn-like rules.
- **Backward chaining** (goal-directed) with simple SLD-style search.
- **Backward rules** can “seed” forward runs: forward premises are proven using backward rules + builtins to produce extra ground facts, then forward chaining continues.

---

## Builtins

Builtins are recognized by expanded IRIs and evaluated during premise/goal checking.

### `math:`

**Arithmetic (list forms unless noted):**

- `math:sum`  
  `(a b c ...) math:sum ?z`  → `z = a + b + c + ...`
- `math:product`  
  `(a b c ...) math:product ?z` → `z = a*b*c*...`
- `math:difference`  
  `(a b) math:difference ?z` → `z = a - b`
- `math:quotient`  
  `(a b) math:quotient ?z` → `z = a / b` (fails on division by 0)
- `math:exponentiation`  
  `(a b) math:exponentiation ?z` → `z = a^b`  
  Also supports **inverse exponent solve**:  
  `(a ?b) math:exponentiation z` → `b = ln(z)/ln(a)` when valid.

**Unary numeric ops:**

- `math:negation`  
  `x math:negation ?y` → `y = -x`  
  `?x math:negation y` → `x = -y`
- `math:absoluteValue`  
  `x math:absoluteValue ?y` → `y = |x|`

**Trig:**

- `math:sin`
- `math:cos`
- `math:asin`
- `math:acos`

(All take a numeric subject and bind/verify the numeric object.)

**Comparisons (binary or list form):**

- `math:greaterThan` (`>`)
- `math:lessThan` (`<`)
- `math:notLessThan` (`>=`)

Binary example:  
`5 math:greaterThan 3.`

List example:  
`(5 3) math:greaterThan true.`

**Pragmatic extensions:**

- If `math:difference` receives `(xsd:date|xsd:dateTime  xsd:date|xsd:dateTime)`, it returns an `xsd:duration`.
- Comparisons accept `xsd:duration` by converting to an approximate number of seconds (years/months approximated).

### `log:`

- `log:equalTo`
- `log:notEqualTo`

### `time:`

- `time:localTime` (legacy CWM/SWAP builtin):  
  `"" time:localTime ?D.` binds `?D` to the current local time as an `xsd:dateTime`.

### `list:`

- `list:append`  
  Concatenates a list of lists into a single list.

  **Form:**  
  `(L1 L2 ... Ln) list:append L.`

  where each `Li` is a (ground) list and `L` is their concatenation.

  **Notes:**

  * Inputs must be bound lists; `list:append` does not invent missing list parts.
  * Matches the SWAP/CWM `list:append` builtin behavior.

- `list:firstRest` *(experimental / not yet specced)*  
  Bidirectional “head/tail” list splitter/constructor.

  **Form:**  
  `L list:firstRest (F R).`

  - Forward: if `L` is a non-empty list, binds `F` to its first element and `R` to the rest.
  - Inverse: if `R` is a list (or list variable), constructs `L` such that its head is `F` and tail is `R`.

---

## Layout

This crate is deliberately small and self-contained:

- `src/main.rs` — lexer, parser, AST, builtins, backward prover, forward fixpoint, CLI

Dependency note:
- Uses `chrono` for `time:localTime` and date/duration math.

---

## Quick start

### Run eyelite on a file

```bash
cargo run --release -- path/to/file.n3
# or after building:
target/release/eyelite path/to/file.n3
```

`eyelite` outputs **only forward-rule derivations** (not the input facts), printed as N3/Turtle.
Predicates equal to `rdf:type` are printed as `a`.

---

## Examples

### Socrates (forward chaining)

Input:

```n3
@prefix rdfs: .
@prefix : .

:Socrates a :Human.
:Human rdfs:subClassOf :Mortal.

{ ?A rdfs:subClassOf ?B. ?S a ?A. } => { ?S a ?B. }.
```

Run:

```bash
target/release/eyelite input/socrates.n3
```

Output:

```n3
@prefix : .
:Socrates a :Mortal .
```

---

### Backward rule + builtin seeding

Input:

```n3
@prefix math: .
@prefix : .

# something is more interesting if it is greater
{ ?X :moreInterestingThan ?Y. } <= { ?X math:greaterThan ?Y. }.

# derivation
{ 5 :moreInterestingThan 3. } => { 5 :isIndeedMoreInterestingThan 3. }.
```

Output:

```n3
@prefix : .
5 :isIndeedMoreInterestingThan 3 .
```

---

### Age checker (dates + durations + time)

Input:

```n3
@prefix xsd: <http://www.w3.org/2001/XMLSchema#>.
@prefix time: <http://www.w3.org/2000/10/swap/time#>.
@prefix math: <http://www.w3.org/2000/10/swap/math#>.
@prefix : <https://example.org/#>.

:patH :birthDay "1944-08-21"^^xsd:date.

{ ?S :ageAbove ?A } <= {
    ?S :birthDay ?B.
    "" time:localTime ?D.
    (?D ?B) math:difference ?F.
    ?F math:greaterThan ?A.
}.

{
    ?S :ageAbove "P80Y"^^xsd:duration.
} => {
    :test :is true.
}.
```

Expected derivation:

```n3
@prefix : <https://example.org/#> .
:test :is true .
```

