#!/usr/bin/env bash

# The module cache must not carry one checkout's .ml into another. Two
# checkouts share a .definition and differ in the .ml beside it. Each build,
# and the program extracted from it, uses its own .ml, whichever is built
# first. The shared store is under $XDG_CACHE_HOME/soma (nothing under
# ~/.cache). An unchanged checkout is not compiled again. A .vo does not
# record either checkout's absolute .ml path.

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
  cat > "$1/greet.definition" <<'EOT'
greet : string -> string.
EOT
  printf 'let greet s = "%s:" ^ s\n' "$2" > "$1/greet.ml"
  cat > "$1/main.soma" <<'EOT'
Import greet.
main : string := greet "own".
EOT
}

build() {
  (cd "$1" && soma build main.soma > "$TMP/build.out" 2> "$TMP/build.err") || {
    cat "$TMP/build.out" "$TMP/build.err"; exit 1;
  }
}

compiling() { grep -c '^Compiling' "$TMP/build.err" || true; }

# the extracted program of $1 prints $2:own, and its greet.ml is its own
run_own() {
  (cd "$1" && soma extract main.soma -o extracted > "$TMP/extract.log" 2>&1) || {
    cat "$TMP/extract.log"; exit 1;
  }
  if ! grep -q "\"$2:\"" "$1/extracted/greet.ml"; then
    echo "$1 extracted another greet.ml:"; cat "$1/extracted/greet.ml"; exit 1
  fi
  (cd "$1/extracted" &&
    ocamlc -w -a -o check.exe soma_nat.ml uint63.ml float64.ml greet.ml soma_bindings.ml prog.mli prog.ml soma_main.ml) || exit 1
  actual="$("$1/extracted/check.exe")"
  if [ "$actual" != "$2:own" ]; then
    printf '%s printed %s, not %s:own\n' "$1" "$actual" "$2"
    exit 1
  fi
}

# $1's greet.vo must not name $2 (an absolute .ml path)
no_abs() {
  if grep -a -F -q "$2" "$1/.soma-cache/greet.vo"; then
    echo "$1/.soma-cache/greet.vo records $2"; exit 1
  fi
}

project a one
project b two
build a
[ "$(compiling)" = 1 ]
build b
[ "$(compiling)" = 1 ]
no_abs a "$TMP/a/greet.ml"
no_abs a "$TMP/b/greet.ml"
no_abs b "$TMP/a/greet.ml"
no_abs b "$TMP/b/greet.ml"
run_own a one
run_own b two

# b first would have been the same: a's program is still a's after b
run_own a one

# identical to a: the store supplies the module, and it still reads a's .ml
# only as the file beside this checkout's .definition
project c one
build c
[ "$(compiling)" = 0 ]
[ -f c/.soma-cache/greet.vo ]
no_abs c "$TMP/a/greet.ml"
no_abs c "$TMP/c/greet.ml"
run_own c one

# a's .ml changes. c, already built, keeps printing its own
printf 'let greet s = "changed:" ^ s\n' > a/greet.ml
build a
[ "$(compiling)" = 1 ]
run_own a changed
run_own c one

[ -d "$XDG_CACHE_HOME/soma" ]
[ -n "$(find "$XDG_CACHE_HOME/soma" -name greet.vo -print)" ]
[ ! -e "$HOME/.cache/soma" ]
[ ! -e "$HOME/.cache/soma-receipts" ]
