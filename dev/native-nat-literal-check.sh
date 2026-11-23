#!/bin/sh
# Closed standard integer literals must share tuples on both OCaml backends;
# arbitrary nat realizers and ordinary Peano extraction must keep their meaning.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
ROCQ=${ROCQ:-$ROOT/_build/install/default/bin/rocq}
WORK=$(mktemp -d "${TMPDIR:-/tmp}/soma-nat-literal.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
cat >"$WORK/standard.v" <<'COQ'
From Stdlib Require Import ExtrOcamlNatInt.
Definition location (_ : unit) := (7, 9).
Definition literal := 7.
Definition dynamic (n : nat) := S n.
Extraction "standard.ml" literal dynamic location.
Extract Inductive nat => "int" [ "0" "(fun n -> Stdlib.Int.add n 2)" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-2))".
Extraction "custom.ml" literal dynamic.
COQ
cat >"$WORK/peano.v" <<'COQ'
From Stdlib Require Import Extraction.
Definition literal := 7.
Extraction "peano.ml" literal.
COQ
(cd "$WORK" && "$ROCQ" compile -q standard.v && "$ROCQ" compile -q peano.v)
cat >"$WORK/check.ml" <<'ML'
let () =
 assert(Standard.literal=7 && Standard.dynamic 7=8);
 assert(Standard.location()==Standard.location());
 assert(Custom.literal=14 && Custom.dynamic 7=9);
 let rec to_int=function Peano.O->0|Peano.S n->1+to_int n in
 assert(to_int Peano.literal=7);
 print_endline "native nat literals: standard tuple identity and custom/Peano extraction semantics passed"
ML
for compiler in ocamlc ocamlopt; do
 (cd "$WORK" && opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- \
  "$compiler" -w -a -o "check-$compiler" standard.mli standard.ml custom.mli custom.ml peano.mli peano.ml check.ml)
 "$WORK/check-$compiler"
done
