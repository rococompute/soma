#!/usr/bin/env bash
# project_cache_key (topbin/soma.ml) follows symbolic links, including
# acyclic ones that leave the project. They must keep being followed: a
# source change reachable only through an alias has to invalidate the
# shared-cache key, and an unchanged project must keep its key across
# repeated builds.
set -euo pipefail

export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
TMP="$(mktemp -d)"
export SOMA_CACHE="$TMP/store"
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$TMP/project" "$TMP/shared" "$SOMA_CACHE"
cd "$TMP/project"

printf 'x : nat := 1.\n' > a.soma
printf 'Import a.\nx.\n' > main.soma
printf 'm : nat := 3.\n' > "$TMP/shared/m.soma"
# A file alias next to its target, and a directory alias out of the project.
ln -s a.soma alias.soma
ln -s ../shared mirror

build() {  # build EXPECTED_VALUE DESCRIPTION
  soma build -v main.soma > "$TMP/out" 2> "$TMP/err" || {
    echo "soma build failed: $3"
    cat "$TMP/out" "$TMP/err"
    exit 1
  }
  grep -q "= $1" "$TMP/out" || { echo "expected = $1: $3"; cat "$TMP/out" "$TMP/err"; exit 1; }
}
compiled() { grep -c '^Compiling' "$TMP/err" || true; }
stored() { find "$SOMA_CACHE" -mindepth 1 -maxdepth 1 -type d | wc -l | tr -d ' '; }

build 1 'aliased project'
[ "$(compiled)" -ge 1 ]
[ "$(stored)" -eq 1 ]

# Repeated build: same key, nothing compiled.
build 1 'repeat'
[ "$(compiled)" -eq 0 ]
[ "$(stored)" -eq 1 ]

# The key alone restores the cache: the aliases are part of it.
rm -rf .soma-cache
build 1 'restored from the store'
[ "$(compiled)" -eq 0 ]
[ "$(stored)" -eq 1 ]

# A change under the directory alias has another key.
printf 'm : nat := 4.\n' > "$TMP/shared/m.soma"
rm -rf .soma-cache
build 1 'changed under the directory alias'
[ "$(compiled)" -ge 1 ]
[ "$(stored)" -eq 2 ]

# A change of the aliased file has another key.
printf 'x : nat := 2.\n' > a.soma
rm -rf .soma-cache
build 2 'changed aliased file'
[ "$(compiled)" -ge 1 ]
[ "$(stored)" -eq 3 ]

# A new source under the directory alias is not ignored.
printf 'n : nat := 5.\n' > "$TMP/shared/n.soma"
rm -rf .soma-cache
build 2 'new source under the directory alias'
[ "$(stored)" -eq 4 ]

# And the key is stable again.
build 2 'repeat after changes'
[ "$(compiled)" -eq 0 ]
[ "$(stored)" -eq 4 ]

echo 'soma project cache symlink aliases: passed'
