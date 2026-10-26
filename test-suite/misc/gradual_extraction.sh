#!/usr/bin/env bash

# Extraction of gradual Rocq: the casts of the extracted code are checked at
# run time, with the same results as in the kernel.

set -e

export PATH=$BIN:$PATH

cd misc/gradual_extraction/

rm -f gradual_prog.ml gradual_prog.mli main.exe main.log
rocq c -q gradual_prog.v
ocamlfind ocamlopt -w -20 gradual_prog.mli gradual_prog.ml main.ml -o main.exe
./main.exe > main.log
diff -u main.out main.log
