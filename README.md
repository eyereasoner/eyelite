# eyelite

A small Notation3 (N3) parser in Rust with a minimal forward-chaining reasoner.

## Features

- Parses a practical subset of N3:
  - `@prefix` / `@base`
  - triples with `;` and `,` lists
  - blank nodes `[]`, collections `()`
  - variables `?x`
  - quoted formulas `{ ... }`
  - implications `{ ... } => { ... }`
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

