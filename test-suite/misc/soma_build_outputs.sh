#!/usr/bin/env bash

# soma build lists the files it made: a file written just before the build,
# in the same second, is not one of them, nor are rocq c's files, which it
# deletes. With -time, it prints the time of each sentence.

set -euo pipefail

export PATH=$BIN:$PATH
export SOMA_MIRAGE_BUILD=0
export SOMA_OCAML_BUILD=0

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

printf 'x : nat := 1.\nx.\n' > main.soma
echo notes > notes.txt
echo data > data.json
soma build main.soma > out.log 2>&1 || { cat out.log; exit 1; }
if grep -q 'notes.txt\|data.json' out.log; then
  echo "soma build listed a file it did not make"; cat out.log; exit 1
fi
[ ! -f main.vo ] && [ ! -f main.glob ]

# -time prints the time of each sentence, which rocq c says on its output
# (and soma build shows only with -v otherwise); the values of bare terms
# are still not shown
soma build main.soma -time > out.log 2>&1 || { cat out.log; exit 1; }
grep -q '^Chars 0 - [0-9]* \[Definition~x~.* secs' out.log || { echo "soma build -time printed no times"; cat out.log; exit 1; }
if grep -q '= 1' out.log; then
  echo "soma build -time printed a value"; cat out.log; exit 1
fi
