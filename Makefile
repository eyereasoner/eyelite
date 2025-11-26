# Makefile for eyelite

SHELL := /bin/bash
BIN := target/release/eyelite
EXAMPLE_DIR := examples
EXAMPLES := $(wildcard $(EXAMPLE_DIR)/*.n3)

.PHONY: all release clean fmt clippy run-examples run-one list-examples

all: release run-examples

release:
	cargo build --release

clean:
	cargo clean

fmt:
	cargo fmt

clippy:
	cargo clippy -- -D warnings

list-examples:
	@echo "Examples:"
	@for f in $(EXAMPLES); do echo "  $$f"; done

# Run all examples, show output and save to examples-output.n3
run-examples: release
	@{ \
		set -euo pipefail; \
		for f in $(EXAMPLES); do \
			echo "# --------------------------------------------------"; \
			echo "# Running $$f"; \
			echo "# --------------------------------------------------"; \
			$(BIN) "$$f"; \
			echo; \
		done; \
		echo "# All examples finished OK."; \
	} 2>&1 | tee examples-output.n3

# Run one example: make run-one FILE=examples/foo.n3
run-one: release
	@if [ -z "$(FILE)" ]; then \
		echo "Usage: make run-one FILE=examples/foo.n3"; \
		exit 1; \
	fi
	@echo "Running $(FILE)"
	@$(BIN) "$(FILE)"

