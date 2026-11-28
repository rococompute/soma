#!/usr/bin/env bash
# Source-only projects must not launder foreign OCaml through extraction.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
mkdir source
cat >source/soma.toml <<'TOML'
[project]
name="source_only_fixture"
version="0.1.0"
TOML
cat >source/adapter.ml <<'ML'
let f x = x
ML
cat >source/adapter.definition <<'SOMA'
f : int -> int.
SOMA
cat >source/main.soma <<'SOMA'
From Corelib Require Import PrimInt63.
Import adapter.
Definition main := f 0.
Verification Properties "" Invariants ""
  Trust "adapter.f; Corelib.Numbers.Cyclic.Int63.PrimInt63.int".
SOMA
cat >project.toml <<'TOML'
[build]
directory="products"
targets=["source"]
source-only=false
[build.extract.source]
source-root="source"
file="main.soma"
verify=true
TOML
soma project build --config project.toml >foreign-allowed.log 2>&1
test -e products/.extract/source/adapter.ml
cp products/.extract/source/prog.ml previous.ml
sed 's/source-only=false/source-only=true/' project.toml >strict.toml
if soma project build --config strict.toml >foreign-rejected.log 2>&1; then exit 1; fi
grep -q 'source-only build cannot copy OCaml source' foreign-rejected.log
cmp products/.extract/source/prog.ml previous.ml
test -z "$(find products/.extract -name '*.stage*' -print)"
sed 's/verify=true/verify=false/' strict.toml >unverified.toml
if soma project plan --config unverified.toml >unverified.log 2>&1; then exit 1; fi
grep -q 'source-only builds require verify=true' unverified.log
# C is deliberately retained in this profile, with the compiler's typed stubs.
rm source/adapter.ml
cat >source/adapter.c <<'C'
#include "adapter.soma.h"
int64_t adapter_f(int64_t value) { return value; }
C
soma project build --config strict.toml >c-allowed.log 2>&1
test -e products/.extract/source/adapter_soma_c.c
grep -q 'adapter_f' products/.extract/source/adapter_soma_c.c
echo 'PASS: source-only profile rejects copied OCaml and unchecked graph nodes, preserves prior products and permits C'
