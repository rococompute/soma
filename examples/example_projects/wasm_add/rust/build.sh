#!/bin/sh
# Builds the modules and puts them next to main.soma: ../add.wasm, which
# add.definition declares, and ../mul.wasm, which has no .definition.
# Needs Rust and its wasm32-unknown-unknown target
# (rustup target add wasm32-unknown-unknown).
set -e
cd "$(dirname "$0")"
for crate in add mul; do
  (cd "$crate" && cargo build --release --target wasm32-unknown-unknown)
  cp "$crate/target/wasm32-unknown-unknown/release/$crate.wasm" "../$crate.wasm"
done
