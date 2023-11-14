#!/usr/bin/env bash
# Exercise shared .definition objects through actual extracted executables,
# without opam, dune, network access, or optional output assertions.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_OCAML_BUILD=0
unset SOMA_CACHE SOMA_PROJECT_ROOT
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
export HOME="$TMP/home"
export XDG_CACHE_HOME="$TMP/xdg"
mkdir -p "$HOME" "$XDG_CACHE_HOME"
cd "$TMP"

fixture() {
  mkdir -p "$1"
  cat > "$1/greet.definition" <<'EOT'
greet : string -> string.
EOT
  printf 'let greet s = "%s:" ^ s\n' "$2" > "$1/greet.ml"
  cat > "$1/main.soma" <<'EOT'
Import greet.
main : string := greet "own source".
EOT
}

build() {
  (cd "$1" && soma build main.soma > build.out 2> build.err) || {
    cat "$1/build.out" "$1/build.err"; exit 1;
  }
}

output() {
  (cd "$1" && soma extract main.soma -o extracted > extract.log 2>&1) || {
    cat "$1/extract.log"; exit 1;
  }
  # This fixture needs only the OCaml standard library. Compile exactly the
  # files Soma emits, including its declaration checks and entry point.
  (cd "$1/extracted" &&
    ocamlc -w -a -o check.exe soma_nat.ml float64.ml greet.ml soma_bindings.ml prog.mli prog.ml soma_main.ml) || exit 1
  actual=$("$TMP/$1/extracted/check.exe")
  if [ "$actual" != "$2:own source" ]; then
    printf '%s: expected %s:own source, got %s\n' "$1" "$2" "$actual"
    exit 1
  fi
}

fixture first first
fixture second second
fixture identical first
build first
build second
output first first
output second second

# Remove the original source entirely: a restored .vo cannot consult it.
rm -rf first
build identical
if grep -q '^Compiling' identical/build.err; then
  echo 'identical sources missed the shared module cache'
  cat identical/build.err
  exit 1
fi
[ -f identical/.soma-cache/greet.vo ]
output identical first

# Assert both placement and absence, rather than accepting an empty cache.
[ -d "$XDG_CACHE_HOME/soma" ]
[ -n "$(find "$XDG_CACHE_HOME/soma" -name greet.vo -print)" ]
[ ! -e "$HOME/.cache/soma" ]
[ ! -e "$HOME/.cache/soma-receipts" ]
