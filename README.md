# n3lite

A small Notation3 (N3) parser in Rust with a minimal forward-chaining reasoner.

This project started as a learning/utility parser for N3 (a superset of Turtle)
and includes enough semantics to run classic examples like “Socrates is mortal”.

## Features

- Parses a practical subset of N3:
  - `@prefix` / `@base`
  - triples with `;` and `,` lists
  - blank nodes `[]`, collections `()`
  - variables `?x`
  - quoted formulas `{ ... }`
  - implications `{ ... } => { ... }`
- Prefix environment + resolution:
  - expands prefixed names to full IRIs
  - supports EYE-style bare `@prefix foo: .` via built-in prefix defaults
- Naive forward chainer for Horn-like rules:
  - conjunction of triple patterns in premise/conclusion
  - saturates a fact set until fixpoint

## Layout

- `src/n3.pest` — Pest grammar
- `src/parser.rs` — parse tree → AST
- `src/ast.rs` — AST types
- `src/resolve.rs` — prefix env + IRI expansion
- `src/reasoner.rs` — tiny forward chainer
- `src/bin/quick_test.rs` — dump AST for a file
- `src/bin/socrates.rs` — runs the Socrates example

## Quick start

Run the Socrates example:

```bash
cargo run --release --bin socrates
```

Expected output includes:

```
Entails Socrates mortal? true
```

