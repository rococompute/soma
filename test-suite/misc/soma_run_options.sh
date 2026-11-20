#!/usr/bin/env bash
# soma run's --mem and --disk are refused, saying why, when malformed,
# before anything is built; anywhere before --, not passed to rocq c.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cd "$WORK"
printf 'Require Import Sandbox.\nmain : io unit := print "hi".\n' > prog.soma
for bad in --mem=0 --mem=lots --disk=data --disk==x.img; do
    if soma run "$bad" prog.soma > out.log 2>&1; then
        echo "soma run $bad passed" >&2; exit 1
    fi
    grep -q 'soma run: --' out.log || { cat out.log >&2; exit 1; }
    ! grep -q 'Unknown option' out.log
done
soma help 2>&1 | grep -q -- "--disk=NAME=FILE"
