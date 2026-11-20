#!/usr/bin/env bash
# A program over Soma.Host in a switch whose OCaml is older than 5.1 is
# refused, saying what it needs, before anything is compiled. The switch's
# record says 4.14.2, so opam is not asked and the switch need not exist.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
export XDG_CACHE_HOME="$WORK/cache"
export SOMA_OCAML_SWITCH="$WORK/old-switch"
mkdir -p "$XDG_CACHE_HOME/soma/ocaml" "$WORK/p"
digest=$(printf '%s' "$SOMA_OCAML_SWITCH" | { md5sum 2>/dev/null || md5; } | cut -d' ' -f1)
printf 'ocaml 4.14.2\ndune 3.17.0\n' > "$XDG_CACHE_HOME/soma/ocaml/installed-$digest"
cd "$WORK/p"
printf '[project]\nname = "p"\nversion = "0.1.0"\n' > soma.toml
printf 'Require Soma.Host.\nmain : unit := Host.print_lines ["hi"].\n' > main.soma
if soma build main.soma > build.log 2>&1; then
    echo 'a Host program was built with OCaml 4.14' >&2; exit 1
fi
grep -q 'needs OCaml 5.1 or later, and the opam switch .* has OCaml 4.14.2' build.log || { cat build.log >&2; exit 1; }
grep -q 'Point SOMA_OCAML_SWITCH at a switch' build.log
