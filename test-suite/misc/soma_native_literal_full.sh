#!/usr/bin/env bash
# Literal-bearing native calls preserve full-application timing and direct arity.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 40 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"' EXIT
cd "$work"
cat > target.ml <<'OCAML'
let observe=ref(fun (_:string)(_ :string)(_ :string)->())
let invoke prefix first second= !observe prefix first second;first
let promise=ref(Lwt.return "")
let async prefix first second= !observe prefix first second;!promise
OCAML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Type scalar := "float".
OCaml Native External Value invoke : string -> string -> string := "Target.invoke" With "prefix" AtFullApplication.
OCaml Native External Value async : string -> string -> promise string := "Target.async" With "prefix" AtFullApplication.
OCaml Native External Value render : PrimInt63.int -> scalar -> string := "Printf.sprintf" With "<%d:%.1f>" AtFullApplication.
Fail OCaml Native External Value not_function : scalar := "Float.zero" With "prefix" AtFullApplication.
Fail OCaml Native External Value injected : string -> string := "Target.invoke; assert false" With "prefix" AtFullApplication.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target.
Definition public_invoke := Native.Export (Native.Call_callback target.invoke tt).
Definition public_async := Native.Export (Native.Call_callback target.async tt).
Definition public_render := Native.Export (Native.Call_callback target.render tt).
Definition main := (public_invoke,public_async,public_render).
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
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cat > check.ml <<'OCAML'
let require text condition=if not condition then failwith text
let original first second=Target.invoke "prefix" first second
let () =
 let first=String.make 1048576 'f' and second=String.make 1048576 's' in
 let calls=ref 0 in
 Target.observe:=(fun prefix a b->incr calls;require "literal"(prefix="prefix");require "borrowed input"(a==first&&b==second));
 let prepared=Prog.public_invoke first in
 require "partial native call is quiet"(!calls=0);
 require "native result is borrowed"(prepared second==first && !calls=1);
 require "fresh first formatter buffer"(Prog.public_render 1 2.="<1:2.0>");
 require "fresh second formatter buffer"(Prog.public_render 3 4.="<3:4.0>");
 let partial=Prog.public_render 5 in require "partial formatter"(partial 6.="<5:6.0>");
 require "reused partial formatter owns a fresh call buffer"(partial 7.="<5:7.0>");
 let fault=Failure "exact full-call fault"in
 Target.observe:=(fun _ _ _->raise fault);
 require "direct exception identity"(try ignore(Prog.public_invoke first second);false with error->error==fault);
 let pending,_=Lwt.task()in Target.promise:=pending;
 let key=Lwt.new_key()in
 Target.observe:=(fun _ _ _->require "dynamic Lwt scope"(Lwt.get key=Some "caller"));
 Lwt.with_value key(Some "caller")(fun()->require "exact native promise"(Prog.public_async first second==pending));
 Lwt.cancel pending;require "native cancellation"(match Lwt.state pending with Lwt.Fail Lwt.Canceled->true|_->false);
 Target.observe:=(fun _ _ _->());
 let allocation fn=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 100000 do ignore(Sys.opaque_identity(fn first second))done;Gc.allocated_bytes()-.start in
 let expected=allocation original and actual=allocation Prog.public_invoke in
 require "no per-call tuple/effect bridge allocation"(expected=actual);
 Printf.printf "PASS: literal native full calls preserve fresh formatter buffers, partial timing, borrowed identities, direct faults/promises/context/cancellation and allocation (%.0f/%.0f bytes).\n" expected actual
OCAML
for compiler in ocamlc ocamlopt; do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml \
  target.ml soma_bindings.ml prog.mli prog.ml check.ml
 "./check-$compiler"
done
