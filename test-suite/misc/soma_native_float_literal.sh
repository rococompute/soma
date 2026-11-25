#!/usr/bin/env bash
# Native scalar data stays static, checked and in its caller's literal pool.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 40 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"' EXIT
cd "$work"
cat > values.definition <<'SOMA'
From Soma Require Import Native.
From Stdlib Require Import Strings.String.
OCaml Native External Type scalar := "float".
OCaml Native Float zero : scalar := "0.".
OCaml Native Float negative_zero : scalar := "-0.".
OCaml Native Float minute : scalar := "60.0".
OCaml Native Float same_minute : scalar := "6e1".
OCaml Native Float fraction : scalar := "0.10000000000000001".
Fail OCaml Native Float text : string := "0.".
Fail OCaml Native Float function : scalar -> scalar := "0.".
Fail OCaml Native Float infinity : scalar := "1e999".
Fail OCaml Native Float nan : scalar := "nan".
Fail OCaml Native Float injected : scalar := "0.; assert false".
Fail OCaml Native Float invalid : scalar := "1..2".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import values.
Definition zero := Native.Export (Native.Call_callback values.zero tt).
Definition negative_zero := Native.Export (Native.Call_callback values.negative_zero tt).
Definition minute := Native.Export (Native.Call_callback values.minute tt).
Definition same_minute := Native.Export (Native.Call_callback values.same_minute tt).
Definition fraction := Native.Export (Native.Call_callback values.fraction tt).
Definition main := (zero,negative_zero,minute,same_minute,fraction).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PYTEST'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes ' in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PYTEST
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/{soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
# Compile the authenticated generated bodies alongside the old literal sites,
# just as an in-unit project renderer does. No expression is rewritten.
{
  printf 'module Soma_bindings = struct\n'
  cat soma_bindings.ml
  printf '\nend\n'
  cat native/prog.ml
  cat <<'OCAML'
let original_zero ()=0.
let original_negative_zero ()=(-0.)
let original_minute ()=60.
let original_same_minute ()=60.
let reference_zero=original_zero() and reference_negative_zero=original_negative_zero()
  and reference_minute=original_minute() and reference_same_minute=original_same_minute()
let zero=zero() and negative_zero=negative_zero() and minute=minute()
  and same_minute=same_minute() and fraction=fraction()
let require name value=if not value then failwith name
let () =
  require "zero bit representation" (Int64.bits_of_float zero=Int64.bits_of_float 0.);
  require "negative zero bit representation" (Int64.bits_of_float negative_zero=Int64.bits_of_float (-0.));
  require "fraction bit representation" (Int64.bits_of_float fraction=Int64.bits_of_float 0.1);
  require "zero shares native constant pool" ((zero==0.)=(reference_zero==0.));
  require "negative zero shares native constant pool" ((negative_zero==(-0.))=(reference_negative_zero==(-0.)));
  require "minute shares native constant pool" ((minute==60.)=(reference_minute==60.));
  require "equivalent spellings share one literal" ((minute==same_minute)=(reference_minute==reference_same_minute));
  Gc.full_major();let before=Gc.allocated_bytes()in
  for _=1 to 100000 do ignore(Sys.opaque_identity minute)done;
  require "no scalar conversion allocation" (Gc.allocated_bytes()-.before<1024.);
  print_endline "PASS: checked native float literals preserve bits, signed zero, in-unit physical pooling and allocation without new logical assumptions."
OCAML
} > check.ml
for compiler in ocamlc ocamlopt; do
  ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
    soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml check.ml
  "./check-$compiler"
done
