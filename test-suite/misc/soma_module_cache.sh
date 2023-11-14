#!/usr/bin/env bash

# The compiled-module cache across checkouts (topbin/soma.ml's shared store,
# vernac/somaImport.ml's project_file, plugins/soma_ocaml): a .definition's
# .vo names the FILE.ml beside it relative to its project, so a .vo that
# one checkout compiled and another restored builds the second checkout's
# FILE.ml, never the first's. Two checkouts that differ only in the .ml each
# build their own; two identical ones share the store; the store is under
# $XDG_CACHE_HOME/soma when it is set, and nothing is under ~/.cache/soma.

set -euo pipefail

export PATH=$BIN:$PATH
export SOMA_OCAML_BUILD=0

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
unset SOMA_CACHE
export HOME="$TMP/home"
export XDG_CACHE_HOME="$TMP/xdg"
mkdir -p "$HOME" "$XDG_CACHE_HOME"

# a project in folder $1 whose greet.ml says $2
project() {
  mkdir -p "$1"
  cat > "$1/greet.definition" <<'EOT'
greet : string -> string.
EOT
  cat > "$1/greet.ml" <<EOT
let greet s = "$2 " ^ s
EOT
  cat > "$1/main.soma" <<'EOT'
Import greet.
main : string := greet "from Soma".
EOT
}

compiled() { grep -c '^Compiling' "$1" || true; }

# the program of folder $1 says $2: the module it was extracted with is its
# own greet.ml, and, with dune, the program it builds prints so
says() {
  (cd "$1" && rm -rf prog-ocaml && soma extract main.soma -o prog-ocaml > ../out.log 2>&1) || { cat out.log; exit 1; }
  if ! grep -q "\"$2 \"" "$1/prog-ocaml/greet.ml"; then
    echo "$1 was built with another greet.ml:"; cat "$1/prog-ocaml/greet.ml"; exit 1
  fi
  if command -v dune > /dev/null; then
    (cd "$1/prog-ocaml" && dune build --profile release 2> ../../dune.log) || { cat dune.log; exit 1; }
    out="$("$1/prog-ocaml/_build/default/soma_main.exe")"
    [ "$out" = "$2 from Soma" ] || { echo "$1 printed \"$out\", not \"$2 from Soma\""; exit 1; }
  fi
}

# 1. the same .definition, another .ml: each builds its own
project a one
project b two
(cd a && soma build main.soma > ../out.log 2> ../err.log) || { cat out.log err.log; exit 1; }
[ "$(compiled err.log)" = 1 ] || { echo "a: greet.definition was not compiled"; cat err.log; exit 1; }
(cd b && soma build main.soma > ../out.log 2> ../err.log) || { cat out.log err.log; exit 1; }
[ "$(compiled err.log)" = 1 ] || { echo "b: greet.definition was not compiled"; cat err.log; exit 1; }
says a one
says b two

# 2. a checkout identical to a gets a's compiled module from the store,
# compiling nothing
project c one
(cd c && soma build main.soma > ../out.log 2> ../err.log) || { cat out.log err.log; exit 1; }
[ "$(compiled err.log)" = 0 ] || { echo "c: an identical checkout was compiled again"; cat err.log; exit 1; }
[ -f c/.soma-cache/greet.vo ] || { echo "c: nothing was restored from the store"; exit 1; }
says c one

# and once a's greet.ml has changed, a checkout of what a was still builds
# its own greet.ml, and not a's, from the .vo a compiled
cat > a/greet.ml <<'EOT'
let greet s = "changed " ^ s
EOT
(cd a && soma build main.soma > ../out.log 2> ../err.log) || { cat out.log err.log; exit 1; }
[ "$(compiled err.log)" = 1 ] || { echo "a: a changed greet.ml was not compiled again"; cat err.log; exit 1; }
says a changed
project d one
(cd d && soma build main.soma > ../out.log 2> ../err.log) || { cat out.log err.log; exit 1; }
[ "$(compiled err.log)" = 0 ] || { echo "d: an identical checkout was compiled again"; cat err.log; exit 1; }
says d one
says c one

# a moved checkout still finds its own greet.ml
mv d moved
says moved one

# 3. the store is under $XDG_CACHE_HOME/soma, and nothing under ~/.cache/soma
[ -n "$(ls "$XDG_CACHE_HOME/soma")" ] || { echo "nothing was stored under \$XDG_CACHE_HOME/soma"; exit 1; }
if [ -e "$HOME/.cache/soma" ] || [ -e "$HOME/.cache/soma-receipts" ]; then
  echo "the cache was written under ~/.cache with XDG_CACHE_HOME set"; ls -R "$HOME/.cache"; exit 1
fi
