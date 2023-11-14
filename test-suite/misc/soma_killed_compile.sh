#!/usr/bin/env bash

# When a module's compile is killed by a signal (SIGKILL, as from the
# OOM killer), soma build names the module and the signal, and the
# importer refers to that line instead of saying the module "does not
# compile (its errors are above)". SOMA_TEST_KILL_COMPILE=<module name>
# makes that module's compile send itself SIGKILL right after it
# starts (toplevel/ccompile.ml).

set -euo pipefail

export PATH=$BIN:$PATH
export SOMA_MIRAGE_BUILD=0
export SOMA_OCAML_BUILD=0

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

printf 'a_value : nat := 41.\n' > A.soma
printf 'Import A.\nb_value : nat := a_value + 1.\n' > B.soma

# without the env var, the build behaves and prints as before
export SOMA_CACHE="$TMP/store-normal"
soma build B.soma > out.log 2> err.log
if grep -q 'SIGKILL' err.log; then
  echo "normal build reported a killed compile"; cat err.log; exit 1
fi

# B imports A: killing A's compile names A and SIGKILL, with no
# claim that errors are above
rm -rf .soma-cache
if SOMA_CACHE="$TMP/store-killed" SOMA_TEST_KILL_COMPILE=A soma build B.soma > out.log 2> err.log; then
  echo "a killed compile did not fail the build"; cat err.log; exit 1
fi
grep -q 'A' err.log
grep -q 'SIGKILL' err.log
grep -q 'A\.soma: compilation was killed by signal SIGKILL' err.log
grep -q 'Cannot import A: A\.soma was killed while compiling (see the line above)' err.log
if grep -q 'its errors are above' err.log; then
  echo "killed compile still claimed errors are above"; cat err.log; exit 1
fi

# a normal compile failure keeps its current output
printf 'broken : nat := undefined_thing.\n' > A.soma
rm -rf .soma-cache
if SOMA_CACHE="$TMP/store-broken" soma build B.soma > out.log 2> err.log; then
  echo "a broken compile did not fail the build"; cat err.log; exit 1
fi
grep -q 'Cannot import A: A.soma does not compile (its errors are above)' err.log
