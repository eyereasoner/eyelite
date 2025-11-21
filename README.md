# eyelite

A small Notation3 (N3) parser in Rust with a lightweight reasoner.

`eyelite` aims to be tiny and hackable while still supporting classic N3
tutorial-style examples.

## Features

### Parsing (practical N3 subset)
- `@prefix` / `@base` directives
- Triples with `;` and `,` lists
- Blank nodes `[]`, collections `()`
- Variables `?x`
- Quoted formulas `{ ... }`
- Implications:
  - `{P} => {C}.` (forward rules)
  - `{C} <= {P}.` (backward rules)
  - `{P} log:implies {C}.` / `{C} log:impliedBy {P}.` (explicit forms)

### Reasoning
- **Backward chaining** (goal-directed)
- **Forward chaining** to fixpoint over forward rules
- Built-ins evaluated during matching:
  - `math:greaterThan` numeric comparison

## CLI

Build and run:

```bash
cargo build --release
target/release/eyelite path/to/file.n3
```

Behavior:

* Prints **only forward-rule derivations** (not the original facts).
* Output is N3/Turtle using the default `:` prefix when available.
* Derived `rdf:type` predicates are printed as `a`.

## Under the hood

1. **Parse → AST**

   * Pest grammar (`src/n3.pest`) parses the input.
   * `parser.rs` builds an AST (`ast.rs`), expanding `;`/`,` lists into triples.

2. **Prefix expansion**

   * `resolve.rs` builds a `PrefixEnv` from explicit directives only.
   * All prefixed names are rewritten into full IRIs before reasoning.

3. **Normalize explicit implication predicates**

   * `normalize.rs` rewrites
     `{P} log:implies {C}.` and `{C} log:impliedBy {P}.`
     into internal implication nodes.
   * This makes them equivalent to `=>` / `<=`.

4. **Extract facts + rules**

   * `reasoner.rs::extract` collects:

     * ground facts (no variables)
     * Horn-style rules (premise/conclusion as conjunctions of triple patterns)
   * Backward rules are flipped internally into forward orientation.

5. **Backward seeding**

   * The CLI proves any **ground premise** of forward rules via backward chaining
     (using backward rules and builtins).
   * Proven premises are added to the fact set.

6. **Forward chaining**

   * Forward rules are applied to fixpoint to derive new triples.
   * Only these newly forward-derived triples are printed.

## Limitations / non-goals (for now)

* Grammar is simplified vs. full W3C N3 EBNF.
* Builtins are a small subset.
* No reasoning over paths `!`/`^`, inverse `<-`, etc. yet.
* No quoted-formula pattern matching in rule bodies yet.

## Extending

* tighten PN_* / IRIREF rules toward full spec
* add more builtins
* nicer output formatting with multiple prefixes
* quoted-formula reasoning (`log:includes`, etc.)

