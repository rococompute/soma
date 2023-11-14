#!/usr/bin/env bash

# soma build --check-fresh FILE says, from metadata alone, whether FILE is
# as its last successful soma build left it: its sources, its imports, its
# configuration and what was compiled into .soma-cache (topbin/soma.ml).
# Missing or uncertain metadata is stale, which needs the normal build.

set -euo pipefail

export PATH=$BIN:$PATH
export SOMA_MIRAGE_BUILD=0
export SOMA_OCAML_BUILD=0
# no shared cache: what is in .soma-cache is this build's
export SOMA_CACHE="$(mktemp -d)"

EXAMPLE="$(cd "$(dirname "$0")/../../examples/example_projects/cached_compilation" && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP" "$SOMA_CACHE"' EXIT
mkdir "$TMP/logs"
cp -R "$EXAMPLE" "$TMP/project"
cd "$TMP/project"
rm -rf .soma-cache
LOG="$TMP/logs"

compiled() { grep -c '^Compiling' "$LOG/err" || true; }
fresh() { soma build --check-fresh main.soma > "$LOG/fresh" 2>&1; }
stale() {
  if fresh; then echo "reported unchanged: $1"; cat "$LOG/fresh"; exit 1; fi
  grep -q "^main.soma: stale: " "$LOG/fresh" || { cat "$LOG/fresh"; exit 1; }
  grep -q -- "$2" "$LOG/fresh" || { echo "expected: $2"; cat "$LOG/fresh"; exit 1; }
}
build() { soma build main.soma > "$LOG/out" 2> "$LOG/err" || { cat "$LOG/out" "$LOG/err"; exit 1; }; }

# never built: no record
stale 'a project never built' 'no record'

# built: unchanged, without compiling anything
build
[ "$(compiled)" = 3 ]
fresh || { cat "$LOG/fresh"; exit 1; }
grep -qx 'main.soma: unchanged' "$LOG/fresh"
[ ! -f main.vo ]
# the check writes nothing: still unchanged, and a build compiles nothing
fresh
build
[ "$(compiled)" = 0 ]
fresh

# another configuration is not the build that was recorded
if soma build --check-fresh -v main.soma > "$LOG/fresh" 2>&1; then
  echo "reported unchanged with -v"; exit 1
fi
if SOMA_REVIEW=1 soma build --check-fresh main.soma > "$LOG/fresh" 2>&1; then
  echo "reported unchanged with another environment"; exit 1
fi
fresh

# an edited imported source is stale, and the build makes it unchanged again
echo 'spare : nat := 0.' >> models/task.soma
stale 'an edited imported source' 'source ./models/task.soma changed'
build
[ "$(compiled)" -ge 1 ]
fresh

# a missing compiled output is stale, and the build compiles it again
rm .soma-cache/tasks.vo
stale 'a missing compiled output' 'compiled output ./tasks.vo is missing'
build
grep -q '^Compiling tasks.soma' "$LOG/err"
fresh

# a compiled output of the same size but other bytes is stale
cp .soma-cache/text.vo "$TMP/text.vo"
printf 'X' | dd of=.soma-cache/text.vo bs=1 seek=100 conv=notrunc 2> /dev/null
stale 'a changed compiled output' 'compiled output ./text.vo changed'
cp "$TMP/text.vo" .soma-cache/text.vo
fresh

# a failed build leaves no record
echo 'oops := undefined_thing.' >> text.soma
if soma build main.soma > "$LOG/out" 2> "$LOG/err"; then echo "the build did not fail"; exit 1; fi
sed -i.bak '/oops/d' text.soma
rm text.soma.bak
stale 'after a failed build' 'no record'

# options that name files elsewhere are uncertain
build
if soma build --check-fresh main.soma -R "$TMP" Other > "$LOG/fresh" 2>&1; then
  echo "reported unchanged with -R"; exit 1
fi
grep -q 'stale: the option -R' "$LOG/fresh"

# an unreadable record, or none, is stale
fresh
for record in .soma-cache/.freshness/*; do echo garbage > "$record"; done
stale 'a garbled record' 'another format'
rm -rf .soma-cache
stale 'a deleted cache' 'no record'
