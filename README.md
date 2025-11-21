# eyelite

A small Notation3 (N3) parser in Rust with a lightweight reasoner.

`eyelite` parses a practical subset of N3 (a superset of Turtle) and supports
both forward- and backward-chaining over simple Horn-style rules, plus a tiny
set of N3 built-ins (currently enough for classic tutorial examples).

## Features

### Parsing (subset of N3)
- `@prefix` / `@base` directives
- Triples with `;` and `,` lists
- Blank nodes `[]`, collections `()`
- Variables `?x`
- Quoted formulas `{ ... }`
- Implications:
  - forward rules `{P} => {C}.`
  - backward rules `{C} <= {P}.`
- Practical prefixed names + IRIs (simplified PN_* for now)

### Prefix environment + IRI resolution
- Expands prefixed names to full IRIs

### Reasoning
- **Forward chaining** to fixpoint over Horn-like rules
- **Backward chaining** (goal-directed) with simple SLD-style search
- Built-in predicate evaluation (toy subset):
  - `math:greaterThan` (used in backward tutorial examples)

## Non-goals / limitations (for now)

- Grammar is intentionally simplified vs. the full W3C N3 EBNF.
- No proof objects, query variables output formatting, or full built-ins catalog yet.
- No special semantics for paths `!`/`^`, inverse `<-`, etc. in reasoning.
- Quoted-formula pattern matching in rules is not implemented (premises are treated as normal triples).

This is meant to be small, hackable, and useful for experiments.

## Layout

- `src/n3.pest` — Pest grammar
- `src/parser.rs` — parse tree → AST
- `src/ast.rs` — AST types
- `src/resolve.rs` — prefix env + prefixed-name/IRI expansion
- `src/reasoner.rs` — forward + backward chaining + builtins
- `src/bin/quick_test.rs` — parse a file and dump the AST
- `src/bin/socrates.rs` — runs the Socrates forward-chaining example
- `src/bin/backward_demo.rs` — runs a backward-rule + builtin query demo

## Quick start

### Run the Socrates example (forward chaining)

```bash
cargo run --release --bin socrates
```

Expected output includes:

```
Entails Socrates mortal? true
```

### Run the backward-rule + builtin example

Given `rules.n3`:

```n3
@prefix math: <http://www.w3.org/2000/10/swap/math#>.
@prefix : <http://example.org/#>.

{
    ?X :moreInterestingThan ?Y.
} <= {
    ?X math:greaterThan ?Y.
}.
```

and `query.n3`:

```n3
@prefix : <http://example.org/#>.

{
    5 :moreInterestingThan 3.
} => {
    5 :moreInterestingThan 3.
}.
```

Run:

```bash
cargo run --release --bin backward_demo -- rules.n3 query.n3
```

Expected output:

```n3
@prefix : <http://example.org/#>.

5 :moreInterestingThan 3 .
```

## Under the hood

### Parsing pipeline

1. **Pest grammar (`n3.pest`)** tokenizes and parses N3 into a parse tree.
2. **AST builder (`parser.rs`)** converts the parse tree into `ast.rs` structures:

   * expands `;` and `,` predicate/object lists into individual triples
   * preserves formulas and implications as structured nodes

### Prefix resolution

`resolve.rs` builds a `PrefixEnv` from directives:

* reads explicit `@prefix` / `@base`
* rewrites all `Term::PrefixedName` into full `Term::Iri` before reasoning

### Rule extraction

`reasoner.rs::extract` produces:

* **ground facts**: triples without variables
* **rules**: implications where premises/conclusions are conjunctions of triple patterns
  Backward rules `{C} <= {P}` are flipped to forward orientation internally (`P => C`)
  so both engines can use them.

### Forward chaining

A naive fixpoint algorithm:

* match rule premises against the current fact set
* produce bindings
* instantiate conclusions into new facts
* repeat until no new facts appear

Great for small examples, simple and predictable.

### Backward chaining

A tiny goal-directed solver:

* queries are encoded as `{Q} => {Q}.`
* tries to prove each goal by:

  1. matching existing facts
  2. matching a rule conclusion, then recursively proving that rule’s premise
* freshens rule variables to avoid collisions
* includes a recursion depth guard to prevent runaway loops

### Builtins

Built-in predicates are recognized by their expanded IRI (e.g., `math:greaterThan`)
and evaluated during premise/goal checking instead of matched to facts.

Current support:

* `math:greaterThan` numeric comparison

