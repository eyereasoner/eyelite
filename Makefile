.PHONY: build socrates backward all clean

build:
	cargo build --release

socrates: build
	target/release/eyelite examples/socrates.n3 > examples/output/socrates.n3

backward: build
	target/release/eyelite examples/backward_demo.n3 > examples/output/backward_demo.n3

french: build
	target/release/eyelite examples/french_cities.n3 > examples/output/french_cities.n3

peano: build
	target/release/eyelite examples/peano.n3 > examples/output/peano.n3

all: socrates backward french peano

clean:
	cargo clean
