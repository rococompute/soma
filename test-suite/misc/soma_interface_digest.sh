#!/usr/bin/env bash

# Interface digests are observational: the existing stamps still decide what
# compiles. In particular, moving declarations by adding a comment is harmless
# to their interface even when their compiled file's locations change.
set -euo pipefail
export PATH=$BIN:$PATH
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
export SOMA_CACHE="$(mktemp -d)"
EXAMPLE="$(cd "$(dirname "$0")/../../examples/example_projects/cached_compilation" && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP" "$SOMA_CACHE"' EXIT
cp -R "$EXAMPLE" "$TMP/project"
cd "$TMP/project"
rm -rf .soma-cache
build() { soma build main.soma > "$TMP/out" 2> "$TMP/err" || { cat "$TMP/out" "$TMP/err"; exit 1; }; }
digests() { cat .soma-cache/.freshness/* | grep '^interface ' | sort; }
task_digest() { digests | grep '^interface models.task '; }
compiled() { grep -c '^Compiling' "$TMP/err" || true; }
build
[ "$(compiled)" = 3 ]
digests > "$TMP/original"
[ "$(wc -l < "$TMP/original")" = 4 ]
task_digest > "$TMP/task"
{ echo '(* Move every source position. *)'; cat models/task.soma; } > "$TMP/source"
cp "$TMP/source" models/task.soma
build
# Current rebuild policy still sees the changed compiled locations.
[ "$(compiled)" = 3 ]
task_digest > "$TMP/comment"
cmp "$TMP/task" "$TMP/comment"
echo 'spare : nat := 0.' >> models/task.soma
build
task_digest > "$TMP/added"
! cmp -s "$TMP/comment" "$TMP/added"
sed -i.bak 's/spare : nat := 0\./spare : bool := false./' models/task.soma
rm models/task.soma.bak
build
task_digest > "$TMP/type"
! cmp -s "$TMP/added" "$TMP/type"
digests > "$TMP/before-clean"
rm -rf .soma-cache "$SOMA_CACHE"/*
build
[ "$(compiled)" = 3 ]
digests > "$TMP/clean"
cmp "$TMP/before-clean" "$TMP/clean"
