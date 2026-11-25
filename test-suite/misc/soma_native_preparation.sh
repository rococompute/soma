#!/usr/bin/env bash
# One-time preparation may expose consumers that produce existing native entries.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 30 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"' EXIT
cd "$work"
cat > effects.ml <<'ML'
let count=ref 0
let prepare ()=incr count;ref 0
let invoke owner value=incr owner;value
ML
cat > effects.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
OCaml Native External Value prepare : unit -> reference PrimInt63.int := "Effects.prepare".
OCaml Native External Value invoke : forall A : Type, reference PrimInt63.int -> A -> A := "Effects.invoke".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
Import effects.
Definition prepared := Native.Prepare
 (Native.Bind (Native.Call_callback prepare tt) (fun allocate =>
  Native.Invoke (fun _ => allocate tt) Native.Return))
 (fun owner => fun (text : reference PrimInt63.int) => Native.Export (
  Native.Bind (Native.Call_callback (invoke _) tt) (fun invoke =>
    Native.tail_invoke (fun _ => invoke owner text)))).
Definition main := prepared.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes ' in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PY
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/{prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml,effects.ml} .
cat > check.ml <<'ML'
let ()=
 if !Effects.count<>1 then failwith "capabilities were not prepared exactly once";
 let payload=ref 71 in
 for _=1 to 1000 do if Prog.prepared payload!=payload then failwith "borrowed result identity" done;
 if !Effects.count<>1 then failwith "consumer reprepared capabilities";
 print_endline "PASS: one native preparation exposes an entry-producing function without a logical evaluator, repeated preparation or borrowed-value copying."
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml effects.ml soma_bindings.ml prog.mli prog.ml check.ml
 "./check-$compiler"
done
cat > inspect.soma <<'SOMA'
From Soma Require Import Native.
Definition inspect (value : Native.preparation nat) :=
 match value with Native.Prepare _ _ => O end.
Definition main := inspect.
SOMA
if soma extract inspect.soma -no-soma-prelude -o inspect >inspect.log 2>&1;then
 echo 'accepted native preparation inspection' >&2;exit 1
fi
grep -q 'cannot be inspected' inspect.log
