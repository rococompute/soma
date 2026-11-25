#!/usr/bin/env bash
# Closed ignored-input assertions preserve typed arguments without changing unit thunk factories.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 50 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat > sites.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native Assertion Function Factory word_site : unit -> PrimInt63.int -> PrimInt63.int := 42 28.
OCaml Native Assertion Function Factory natural_site : unit -> nat -> PrimInt63.int := 43 5.
OCaml Native Assertion Function Factory text_site : unit -> string -> string := 44 7.
OCaml Native Assertion Function Factory pending_site : unit -> string -> promise PrimInt63.int := 45 9.
OCaml Native Assertion Function Factory callback_site : unit -> (unit -> PrimInt63.int) -> bool := 46 11.
OCaml Native Assertion Function Factory unit_site : unit -> unit -> bool := 47 13.
OCaml Native Assertion Function Factory universal : forall A B:Type, unit -> A -> B := 48 0.
Fail OCaml Native Assertion Function Factory missing_factory : PrimInt63.int -> PrimInt63.int := 42 28.
Fail OCaml Native Assertion Function Factory missing_function : unit -> PrimInt63.int := 42 28.
Fail OCaml Native Assertion Function Factory first_argument : PrimInt63.int -> string -> bool := 42 28.
Fail OCaml Native Assertion Function Factory labelled_factory : forall (arg:unit), string -> bool := 42 28.
Fail OCaml Native Assertion Function Factory labelled_input : unit -> forall (arg:string), bool := 42 28.
Fail OCaml Native Assertion Function Factory late_type : unit -> forall A:Type, A -> A := 42 28.
Fail OCaml Native Assertion Function Factory zero_line : unit -> string -> bool := 0 0.
(* The original unit-only command retains its original rejection contract. *)
Fail OCaml Native Assertion Factory nonunit_old : unit -> PrimInt63.int -> bool := 42 28.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
Import sites.
Definition factory := Native.Export (Native.Call_callback word_site tt).
Definition natural := Native.Export (Native.Call_callback natural_site tt).
Definition text := Native.Export (Native.Call_callback text_site tt).
Definition pending := Native.Export (Native.Call_callback pending_site tt).
Definition callback_value := Native.Export (Native.Call_callback callback_site tt).
Definition unit_input := Native.Export (Native.Call_callback unit_site tt).
Definition polymorphic := Native.Export (Native.Call_callback (universal string PrimInt63.int) tt).
Definition main := (factory,natural,text,pending,callback_value,unit_input,polymorphic).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
assert 'fun () -> fun _ -> Stdlib.raise (Stdlib.Assert_failure (__FILE__, 42, 28))'in Path('native/soma_bindings.ml').read_text()
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
{
 printf '# 1 "assertion-function-fixture.ml"\nmodule Soma_bindings=struct\n'
 cat native/soma_bindings.ml
 printf '\nend\n'
 cat native/prog.ml
 cat <<'ML'
# 42 "assertion-function-fixture.ml"
let original () = (fun _ -> assert false)
# 100 "assertion-function-fixture.ml"
let require name value=if not value then failwith name
let catch f value=try ignore(f value);failwith "assertion returned"with error->error
let location=function Assert_failure where->where|error->raise error
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let a=original()and b=original()and x=factory()and y=factory()in
 require "closed function sharing and creation"((a==b)=(x==y));
 let old=catch a 0 and current=catch x 0 in
 require "exact assertion file/line/column"(location old=location current&&location current=("assertion-function-fixture.ml",42,28));
 require "fresh synchronous exception per call"(old!=catch a 1&&current!=catch x 1);
 let old_file,_,_=location old and current_file,_,_=location current in
 require "original in-unit filename pooling"((old_file=="assertion-function-fixture.ml")=(current_file=="assertion-function-fixture.ml"));
 let check line column f input=require "typed ignored input and result"(location(catch f input)=("assertion-function-fixture.ml",line,column))in
 check 43 5(natural())0;check 44 7(text())"borrowed";check 45 9(pending())"promise";
 let invoked=ref false in check 46 11(callback_value())(fun()->invoked:=true;7);require "ignored callback never invoked"(not !invoked);
 check 47 13(unit_input())();check 48 0(polymorphic())"polymorphic input";
 let measure fn=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do fn()done;Gc.allocated_bytes()-.before in
 let before=measure(fun()->ignore(Sys.opaque_identity(original())))and after=measure(fun()->ignore(Sys.opaque_identity(factory())))in
 require "factory allocation parity"(before=after);
 let failure_before=measure(fun()->ignore(Sys.opaque_identity(catch a 7)))and failure_after=measure(fun()->ignore(Sys.opaque_identity(catch x 7)))in
 require "failed call allocation parity"(failure_before=failure_after);
 let large=String.make(64*1024*1024)'x'in
 let old=original()and current=text()in
 let failed_old=measure(fun()->ignore(Sys.opaque_identity(catch old large)))and failed_current=measure(fun()->ignore(Sys.opaque_identity(catch current large)))in
 require "ignored 64MiB input never copied"(failed_old=failed_current);
 let weak fn=let slot=Weak.create 1 in
  let[@inline never] call()=let input=Bytes.create 1048576 in Weak.set slot 0(Some input);ignore(catch fn input)in
  call();collect();Weak.check slot 0 in
 let generic : bytes->int=universal () ()in
 require "ignored input released after raise"(not(weak(original()))&&not(weak generic));
 Printf.printf "PASS: ignored-input assertion functions preserve native/bytecode sharing, exact location/pooling, fresh synchronous exceptions, native argument/result types and ownership; factory %.0f/%.0f and failure %.0f/%.0f B allocations.\n%!"before after failure_before failure_after
ML
} > check.ml
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest baseline-abi
cp hash.log baseline-hashes
sed -i.bak 's/word_site : unit -> PrimInt63.int -> PrimInt63.int := 42 28/word_site : unit -> PrimInt63.int -> PrimInt63.int := 49 28/' sites.definition
soma extract main.soma -no-soma-prelude -o changed-native >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hashes
if cmp -s baseline-abi changed-native/native_abi.manifest;then echo 'ignored-input assertion location missing from native ABI' >&2;exit 1;fi
python3 - <<'PY'
from pathlib import Path
def hashes(path):return {line.split()[2]:line.split()[:2]for line in Path(path).read_text().splitlines()if len(line.split())>=3}
a=hashes('baseline-hashes');b=hashes('changed-hashes')
for key in ('sites.word_site','main.factory','main.main'):
 assert a[key][0]!=b[key][0] and a[key][1]!=b[key][1],(key,a[key],b[key])
PY
