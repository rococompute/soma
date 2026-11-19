#!/usr/bin/env bash
# Compile the unmodified production helper and actual no-replace native stub.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
for module in somaMerkle somaCache somaModuleStore; do
  cp "$ROOT/clib/$module.ml" "$ROOT/clib/$module.mli" "$TMP/"
done
cp "$ROOT/clib/soma_cache_fs.c" "$TMP/"
cp "$(dirname "$0")/soma_module_donor_trust.ml" "$TMP/main.ml"
cd "$TMP"
mkdir receipts
export XDG_CACHE_HOME="$TMP/receipts" SOMA_CACHE_ID=donor-trust-test
ocamlfind ocamlc -package digestif.c,unix -c somaMerkle.mli somaMerkle.ml somaCache.mli somaCache.ml somaModuleStore.mli somaModuleStore.ml
ocamlfind ocamlc -custom -package digestif.c,unix -linkpkg soma_cache_fs.c somaMerkle.cmo somaCache.cmo somaModuleStore.cmo main.ml -o regression
./regression
