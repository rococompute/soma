#!/usr/bin/env bash
# --no-image participates in the build configuration even though it is
# consumed by the driver before the compiler sees its arguments.
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
export SOMA_CACHE="$WORK/cache"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE SOMA_MIRAGE_SWITCH
mkdir "$WORK/project"
cd "$WORK/project"
printf 'greeting := "hello".\n' > helper.soma
printf 'Import helper.\n' > mirage_minimal.soma
cat "$ROOT/examples/example_files/mirage_minimal/mirage_minimal.soma" >> mirage_minimal.soma
# The explicit request must not reuse the driver's record of a build made
# without that option. Also check that malformed extracted code is rejected.
REAL_OCAMLC=$(command -v ocamlc)
export REAL_OCAMLC
mkdir "$WORK/compiler"
cat > "$WORK/compiler/ocamlc" <<'WRAPPER'
#!/bin/sh
case " $* " in
  *' -open Standins '*)
    [ "${INJECT_BROKEN:-0}" = 0 ] || printf '\nlet broken : string = 42\n' >> prog.ml ;;
esac
exec "$REAL_OCAMLC" "$@"
WRAPPER
chmod +x "$WORK/compiler/ocamlc"
soma build mirage_minimal.soma > "$WORK/fallback.log" 2>&1
grep -q '(no image)' "$WORK/fallback.log"
grep -q '^flags .*no_image=false$' .soma-cache/.freshness/*
soma build mirage_minimal.soma > "$WORK/unchanged.log" 2>&1
grep -q 'unchanged since its last build' "$WORK/unchanged.log"
soma build --no-image mirage_minimal.soma > "$WORK/explicit-native.log" 2>&1
grep -q '(no image)' "$WORK/explicit-native.log"
grep -q '^flags .*no_image=true$' .soma-cache/.freshness/*
export PATH="$WORK/compiler:$PATH"
if INJECT_BROKEN=1 soma build --no-image mirage_minimal.soma > "$WORK/broken.log" 2>&1; then
    echo '--no-image reused another build configuration or accepted ill-typed prog.ml' >&2
    exit 1
fi
grep -q 'prog.ml' "$WORK/broken.log"
grep -q 'Error:' "$WORK/broken.log"
soma build --no-image mirage_minimal.soma > "$WORK/explicit.log" 2>&1
grep -q '(no image)' "$WORK/explicit.log"
# The wrapper executes a compiler outside its own script. Its dependency
# closure is unknown, so a successful wrapped check stays uncertified.
if soma build --check-fresh --no-image mirage_minimal.soma > "$WORK/wrapper-fresh.log" 2>&1; then
    echo 'an opaque compiler wrapper was certified for skipping' >&2
    exit 1
fi
[ ! -f mirage_minimal.hvt ]
