#!/usr/bin/env bash

# The shared store of compiled projects (topbin/soma.ml) keys a project by
# its own files. A dependency on a folder ({ path = "../wip" }) is outside
# them, so such a project is not kept in the store: two checkouts of it,
# each beside its own ../wip, build each their own. A project without one
# is still stored.

set -euo pipefail

export PATH=$BIN:$PATH
export SOMA_OCAML_BUILD=0

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
TMP="$(pwd -P)"
unset SOMA_CACHE
export HOME="$TMP/home"
export XDG_CACHE_HOME="$TMP/xdg"
mkdir -p "$HOME" "$XDG_CACHE_HOME"

# the store's entries: folders named by a SHA256 key, 64 hexadecimal digits
entries() {
  if [ -d "$XDG_CACHE_HOME/soma" ]; then
    ls "$XDG_CACHE_HOME/soma" | grep -c '^[0-9a-f]\{64\}$' || true
  else
    echo 0
  fi
}

# checkout $1: an app whose ../wip defines w as $2
checkout() {
  mkdir -p "$TMP/$1/wip" "$TMP/$1/app"
  printf '[project]\nname = "wip"\nversion = "0.1.0"\n' > "$TMP/$1/wip/soma.toml"
  echo "w : nat := $2." > "$TMP/$1/wip/w.soma"
  printf '[project]\nname = "app"\nversion = "0.1.0"\n\n[dependencies]\n"owner/wip" = { path = "../wip" }\n' > "$TMP/$1/app/soma.toml"
  printf 'Import wip.w.\nw.\n' > "$TMP/$1/app/main.soma"
}

built() {
  (cd "$TMP/$1/app" && soma build -v main.soma > "$TMP/out.log" 2>&1) || { cat "$TMP/out.log"; exit 1; }
  grep -q -- "= $2" "$TMP/out.log" || { echo "$1 did not print = $2:"; cat "$TMP/out.log"; exit 1; }
}

checkout x 3
checkout y 5
built x 3
built y 5
[ "$(entries)" = 0 ] || { echo "a project with a path dependency was stored:"; ls "$XDG_CACHE_HOME/soma"; exit 1; }

# a project without one is stored
mkdir -p "$TMP/plain"
printf '[project]\nname = "plain"\nversion = "0.1.0"\n' > "$TMP/plain/soma.toml"
printf 'seven : nat := 7.\n' > "$TMP/plain/numbers.soma"
printf 'Import numbers.\nseven.\n' > "$TMP/plain/main.soma"
(cd "$TMP/plain" && soma build -v main.soma > "$TMP/out.log" 2>&1) || { cat "$TMP/out.log"; exit 1; }
grep -q -- "= 7" "$TMP/out.log" || { cat "$TMP/out.log"; exit 1; }
[ "$(entries)" = 1 ] || { echo "the project was not stored:"; ls -a "$XDG_CACHE_HOME/soma" || true; exit 1; }
[ ! -e "$HOME/.cache/soma" ] || { echo "written under ~/.cache/soma"; exit 1; }
