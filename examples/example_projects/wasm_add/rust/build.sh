#!/bin/sh
# Builds the module and puts it next to add.definition: ../add.wasm.
# Needs Rust and its wasm32-unknown-unknown target
# (rustup target add wasm32-unknown-unknown).
set -e
cd "$(dirname "$0")"
cargo build --release --target wasm32-unknown-unknown
cp target/wasm32-unknown-unknown/release/add.wasm ../add.wasm
