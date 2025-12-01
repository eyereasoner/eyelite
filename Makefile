# Makefile for eyeling

SHELL := /bin/bash
BIN := target/release/eyeling
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
			if [ "$$f" = "examples/fuse.n3" ]; then \
				# Fuse example: we EXPECT exit code 2. \
				set +e; \
				$(BIN) "$$f"; status=$$?; \
				set -e; \
				if [ $$status -ne 2 ]; then \
					echo "Unexpected exit code $$status for $$f" >&2; \
					exit $$status; \
				fi; \
			else \
				$(BIN) "$$f"; \
			fi; \
			echo; \
		done; \
		echo "# All $(words $(EXAMPLES)) examples finished OK."; \
	} 2>&1 | tee examples-output.n3

# Run one example: make run-one FILE=examples/foo.n3
run-one: release
	@if [ -z "$(FILE)" ]; then \
		echo "Usage: make run-one FILE=examples/foo.n3"; \
		exit 1; \
	fi
	@echo "Running $(FILE)"
	@$(BIN) "$(FILE)"

