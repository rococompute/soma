#!/usr/bin/env bash
# Extraction plus optional real Lwt/Solo5 execution (no model calls).
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 40 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
cp "$ROOT/examples/example_files/mirage_async_control/mirage_async_control.soma" "$WORK/main.soma"
cat > "$WORK/exit.soma" <<'SOMA'
Require Import Sandbox.
main : io unit := r <- attempt (exit 7 : io unit) ;; print "exit swallowed" ;; exit 1.
SOMA
cd "$WORK"
if [ "${SOMA_TEST_HVF:-0}" = 1 ]; then
    soma build main.soma > build.log 2>&1
    timeout 20 opam exec --switch="${SOMA_MIRAGE_SWITCH:-hvf}" -- solo5-hvt --mem=256 -- main.hvt > boot.log 2>&1
    grep -q 'async control and task context verified' boot.log
    soma build exit.soma > exit-build.log 2>&1
    set +e
    timeout 20 opam exec --switch="${SOMA_MIRAGE_SWITCH:-hvf}" -- solo5-hvt --mem=256 -- exit.hvt > exit-boot.log 2>&1
    rc=$?
    set -e
    [ "$rc" = 7 ]
    ! grep -q 'exit swallowed' exit-boot.log
else
    export SOMA_MIRAGE_DIR="$WORK/mirage"
    soma build --no-image main.soma > build.log 2>&1
    soma build --no-image exit.soma > exit-build.log 2>&1
fi
echo 'async control: ok'
