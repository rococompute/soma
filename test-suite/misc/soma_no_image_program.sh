#!/usr/bin/env bash
# Reject a program's own extracted Mirage interface misuse, without a
# compiler wrapper or changes to the generated runtime.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE SOMA_MIRAGE_SWITCH
cd "$WORK"
cat > good.soma <<'SOMA'
Require Import Sandbox.
Axiom message : string.
Extract Constant message => """""".
Definition main : io unit := print message.
SOMA
cat > bad.soma <<'SOMA'
Require Import Sandbox.
Axiom message : string.
Extract Constant message => "(Mirage_sleep.ns ""not a duration"")".
Definition main : io unit := print message.
SOMA
# Separate source names ensure both paths compile even if build freshness
# starts skipping unchanged programs in the future.
cp good.soma fallback_good.soma
cp bad.soma fallback_bad.soma
for mode in explicit fallback; do
    if [ "$mode" = explicit ]; then
        flags=(--no-image)
        good=good
        bad=bad
        export SOMA_MIRAGE_SWITCH=nonexistent
    else
        flags=()
        good=fallback_good
        bad=fallback_bad
        unset SOMA_MIRAGE_SWITCH
    fi
    soma build "${flags[@]}" "$good.soma" > "$mode-good.log" 2>&1
    grep -q '(no image)' "$mode-good.log"
    test -f "$SOMA_MIRAGE_DIR/plain/config.ml"
    test -f "$SOMA_MIRAGE_DIR/plain/prog.ml"
    test -f "$SOMA_MIRAGE_DIR/plain/no-image/soma_rt.cmo"
    test ! -e "$good.hvt"
    if soma build "${flags[@]}" "$bad.soma" > "$mode-bad.log" 2>&1; then
        echo 'ill-typed extracted program passed the Sandbox check' >&2
        exit 1
    fi
    grep -q 'OCaml check failed' "$mode-bad.log"
    grep -q 'prog.ml' "$mode-bad.log"
    grep -q 'Error:' "$mode-bad.log"
    grep -q 'int64' "$mode-bad.log"
    test ! -e "$bad.hvt"
    test ! -e "$SOMA_MIRAGE_DIR/plain/dist/soma.hvt"
done
