build:
	cargo build

all: build

help:
	@echo "usage: make $(prog) [debug=1]"

test:
	cargo build
	cargo test

bench:
	cargo build
	cargo bench

.PHONY: build all help test bench
