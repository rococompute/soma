#!/usr/bin/env bash

# A Rocq library (plugins/soma_rocq): [Rocq Library "mylib" in "DIR".]
# compiles it from its source with Soma, once, into the project's cache, and puts
# its theories in the load path: a Soma program computes with its
# definitions and proves with its lemmas. (From opam, [Rocq Library
# "rocq-stdpp".], it is the same, its source fetched by opam source.)

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
export XDG_CACHE_HOME="$TMP/cache"

mkdir -p mylib/theories prog
printf 'Definition two := 2.\n' > mylib/theories/A.v
cat > mylib/theories/B.v <<'EOT'
From mylib Require Import A.
Definition four := two + two.
Lemma four_is : four = 4. Proof. reflexivity. Qed.
EOT
printf '(rocq.theory\n (name mylib)\n (package mylib))\n' > mylib/theories/dune

cat > prog/main.soma <<'EOT'
Rocq Library "mylib" in "../mylib".
From mylib Require Import B.
eight := four + four.
eight.
EOT
cat > prog/main.proof <<'EOT'
Theorem eight_is : eight = 8.
Proof.
  We need to show that four + four = 8.
  By four_is, we conclude that four + four = 8.
Qed.
EOT
soma build -v prog/main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q 'Rocq: compiling mylib-local-.*: 2/2 mylib/B.v' out.log
grep -q '= 8' out.log
# compiled into the project's cache, and nowhere else
ls prog/.soma-cache/rocq/mylib-local-*/theories > /dev/null
[ ! -e "$XDG_CACHE_HOME/soma/rocq" ]
# the library's source is as it was
[ "$(ls mylib/theories)" = "$(printf 'A.v\nB.v\ndune')" ]

# once: the second build does not compile it again
soma build prog/main.soma > out.log 2>&1 || { cat out.log; exit 1; }
if grep -q 'Rocq: compiling' out.log; then echo "the library was compiled again"; exit 1; fi

# a change to its source compiles it again
printf 'Definition two := 2.\nDefinition three := 3.\n' > mylib/theories/A.v
soma build prog/main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q 'Rocq: compiling' out.log

# a library that loads an OCaml plugin is refused, on the parsed command:
# however it is spaced or commented (SECURITY-REVIEW.md "Known limits")
plugin_refused() {
  printf '%b' "$2" > mylib/theories/C.v
  if soma build prog/main.soma > out.log 2>&1; then echo "a plugin was loaded ($1)"; cat out.log; exit 1; fi
  grep -q 'loads an OCaml plugin (C.v)' out.log || { echo "missing error ($1)"; cat out.log; exit 1; }
}
plugin_refused 'ordinary' 'Declare ML Module "some.plugin".\n'
plugin_refused 'spaces' 'Declare  ML   Module "some.plugin".\n'
plugin_refused 'newlines and tabs' 'Declare\n\tML\nModule\n"some.plugin".\n'
plugin_refused 'comments' 'Declare (* x *) ML (* y\n*) Module "some.plugin".\n'
plugin_refused 'locality' 'Local Declare ML Module "some.plugin".\n'

# the words in a comment or a string are no command: the library compiles
cat > mylib/theories/C.v <<'EOT'
(* Declare ML Module "some.plugin". *)
Comments "Declare ML Module" "some.plugin".
Definition five := 5.
EOT
soma build prog/main.soma > out.log 2>&1 || { echo "a comment or string was refused"; cat out.log; exit 1; }
grep -q 'Rocq: compiling mylib-local-.*mylib/C.v' out.log
rm mylib/theories/C.v

# a source without theories
mkdir empty
printf 'Rocq Library "none" in "../empty".\n' > prog/none.soma
if soma build prog/none.soma > out.log 2>&1; then echo "a library without theories was taken"; exit 1; fi
grep -q 'none declares no theory' out.log
