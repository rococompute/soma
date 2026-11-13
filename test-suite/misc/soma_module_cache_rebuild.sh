#!/usr/bin/env bash

# The shared module store, with the checkout that differs built first.
# Two checkouts share a .definition and differ in the .ml beside it
# (a function returning 1, and one returning 2). Each build, and the
# program extracted from it, uses its own .ml. Rebuilding an unchanged
# checkout does not compile again. The store is under $XDG_CACHE_HOME/soma
# and not under ~/.cache. With XDG_CACHE_HOME unset it is under ~/.cache/soma.
# soma build --no-module-cache neither reads nor writes the store.

set -euo pipefail

export PATH="$BIN:$PATH"
export SOMA_OCAML_BUILD=0
unset SOMA_CACHE SOMA_PROJECT_ROOT SOMA_BUILD_ROOT SOMA_PROJECT_PREFIX

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
export HOME="$TMP/home"
export XDG_CACHE_HOME="$TMP/xdg"
mkdir -p "$HOME" "$XDG_CACHE_HOME"

project() {
  mkdir -p "$1"
  cat > "$1/answer.definition" <<'EOT'
answer : string -> string.
EOT
  printf 'let answer _ = "%s"\n' "$2" > "$1/answer.ml"
  cat > "$1/main.soma" <<'EOT'
Import answer.
main : string := answer "x".
EOT
}

build() {
  (cd "$1" && soma build main.soma > "$TMP/build.out" 2> "$TMP/build.err") || {
    cat "$TMP/build.out" "$TMP/build.err"; exit 1;
  }
}

build_nocache() {
  (cd "$1" && soma build --no-module-cache main.soma > "$TMP/build.out" 2> "$TMP/build.err") || {
    cat "$TMP/build.out" "$TMP/build.err"; exit 1;
  }
}

compiling() { grep -c '^Compiling' "$TMP/build.err" || true; }

entries() {
  if [ -d "$XDG_CACHE_HOME/soma" ]; then
    ls "$XDG_CACHE_HOME/soma" | grep -c '^[0-9a-f]\{32\}$' || true
  else
    echo 0
  fi
}

# the extracted program of $1 prints $2, from its own answer.ml
run_own() {
  (cd "$1" && soma extract main.soma -o extracted > "$TMP/extract.log" 2>&1) || {
    cat "$TMP/extract.log"; exit 1;
  }
  if ! grep -q "\"$2\"" "$1/extracted/answer.ml"; then
    echo "$1 extracted another answer.ml:"; cat "$1/extracted/answer.ml"; exit 1
  fi
  (cd "$1/extracted" &&
    ocamlc -w -a -o check.exe soma_nat.ml uint63.ml float64.ml answer.ml soma_bindings.ml prog.mli prog.ml soma_main.ml) || exit 1
  actual="$("$1/extracted/check.exe")"
  if [ "$actual" != "$2" ]; then
    printf '%s printed %s, not %s\n' "$1" "$actual" "$2"
    exit 1
  fi
}

no_abs() {
  if grep -a -F -q "$2" "$1/.soma-cache/answer.vo"; then
    echo "$1/.soma-cache/answer.vo records $2"; exit 1
  fi
}

# the checkout that returns 2 is built first
project two 2
build two
[ "$(compiling)" = 1 ]
project one 1
build one
[ "$(compiling)" = 1 ]
no_abs two "$TMP/two/answer.ml"
no_abs two "$TMP/one/answer.ml"
no_abs one "$TMP/two/answer.ml"
no_abs one "$TMP/one/answer.ml"
run_own two 2
run_own one 1
run_own two 2

# unchanged two is not compiled again
build two
[ "$(compiling)" = 0 ]
run_own two 2

[ -d "$XDG_CACHE_HOME/soma" ]
[ -n "$(find "$XDG_CACHE_HOME/soma" -name answer.vo -print)" ]
[ ! -e "$HOME/.cache/soma" ]
[ ! -e "$HOME/.cache/soma-receipts" ]

# identical to two, but the shared store is not consulted
project same 2
build_nocache same
[ "$(compiling)" = 1 ]
run_own same 2

# a project never stored is not published when the store is off
before="$(entries)"
project only 9
build_nocache only
[ "$(compiling)" = 1 ]
[ "$(entries)" = "$before" ]
run_own only 9

# unset XDG_CACHE_HOME: the store falls back to ~/.cache/soma
unset XDG_CACHE_HOME
project fallback 4
build fallback
[ "$(compiling)" = 1 ]
[ -n "$(find "$HOME/.cache/soma" -name answer.vo -print)" ]
run_own fallback 4
