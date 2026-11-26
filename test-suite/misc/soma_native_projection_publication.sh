#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 24 "$work"/*.log 2>/dev/null||true;fi;if [ "${KEEP:-0}" = 1 ];then echo "Retained $work";else rm -rf "$work";fi;exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type owner={cell:bytes option ref;pending:bytes Lwt.t;mutable fault:exn option}
let key:int Lwt.key=Lwt.new_key()
let seen=ref None
let run owner (payload:bytes)=seen:=Lwt.get key;ignore(Sys.opaque_identity payload);match owner.fault with Some error->raise error|None->owner.pending
let cell:bytes option ref=ref None
let bundle=Lwt.return,([],(cell,(run,true)))
let marker=17
let triple=(1,2,3)
let original_cell:bytes option ref=ref None
let replacement_cell:bytes option ref=ref None
type holder={mutable tuple:bytes option ref*int}
let holder={tuple=original_cell,41}
let dynamic()=failwith "runtime projection getter ran"
ML
cat >target.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native External Value marker : unit := "Stdlib.ignore" With "unused".
SOMA
cat >bindings.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List.
OCaml Native External Type bytes := "Bytes.t".
OCaml Native External Type owner := "Target.owner".
OCaml Native External Value tuple_value : forall A B:Type,
 ((A->promise A)*(list B*(reference(option bytes)*((owner->bytes->promise bytes)*bool)))) := "Target.bundle".
OCaml Native External Value scalar_value : PrimInt63.int := "Target.marker".
OCaml Native Reexport Binding before := scalar_value.
OCaml Native Reexport Projection commands := tuple_value As "(ret, (empty, (cell, (run, _))))".
OCaml Native Reexport Binding after := scalar_value.
OCaml Native Projected Value read_run : owner->bytes->promise bytes := commands Member "run".
OCaml Native Projected Value read_ret : forall A:Type,A->promise A := commands Member "ret".
OCaml Native Projected Value read_empty : forall B:Type,list B := commands Member "empty".
Fail OCaml Native Projected Value invalid_type : bytes := commands Member "run".
Fail OCaml Native Projected Value invalid_member : bytes := commands Member "missing".
Fail OCaml Native Projected Value invalid_owner : bytes := scalar_value Member "run".
Fail OCaml Native Reexport Projection duplicate := tuple_value As "(ret, _)".
Fail OCaml Native Reexport Binding run := scalar_value.
Fail OCaml Native Reexport Projection wrong_shape := tuple_value As "(a,b,c)".
Fail OCaml Native Reexport Projection repeated := tuple_value As "(x,(x,_))".
Fail OCaml Native Reexport Projection injected := tuple_value As "(x,_) in failwith".
OCaml Native External Callback dynamic : unit->bool := "Target.dynamic".
Fail OCaml Native Reexport Projection invalid_dynamic := dynamic As "value".
SOMA
cat >only.definition <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
OCaml Native External Value triple_value : Native.triple PrimInt63.int PrimInt63.int PrimInt63.int := "Target.triple".
OCaml Native Reexport Projection members := triple_value As "(first, _, third)".
From Soma Require Import Handles.
OCaml Native External Type bytes := "Bytes.t".
OCaml Native External Field Value holder_value : reference(option bytes)*PrimInt63.int := "Target.holder.tuple".
OCaml Native Reexport Projection holder_members := holder_value As "(borrowed_cell, borrowed_count)".
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native.
Import target bindings only.
Definition run := Native.Export(Native.Call_callback read_run tt).
Definition main := (before,commands,after,members,run,Native.Export(Native.Call_callback marker tt)).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
rows=Path('native/native_binding_projections.manifest').read_text().splitlines()
assert rows[0]=='soma-native-binding-projections-v1'
rows=[shlex.split(row)for row in rows[1:]];assert len(rows)==3
assert [row[6]for row in rows]==['ret,empty,cell,run','first,third','borrowed_cell,borrowed_count']
assert [row[8]for row in rows]==['1','0','1']
for symbol,ns,source,digest,file,product,names,owner,order in rows:
 assert hashlib.sha256(Path(source).read_bytes()).hexdigest()==digest
 assert hashlib.sha256(Path('native',file).read_bytes()).hexdigest()==product
 Path('raw.ml'if ns=='bindings'else'only_raw.ml').write_bytes(Path('native',file).read_bytes())
assert len(list(Path('native').glob('soma_published_*.ml')))==2
assert all('  assumes 'not in line or line.split('  assumes ',1)[1]=='Corelib.Numbers.Cyclic.Int63.PrimInt63.int'for line in Path('hash.log').read_text().splitlines())
PY
(cd native&&dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_bindings.ml,soma_bindings.mli,prog.ml,prog.mli} .
cp native/soma_published_*.ml .
cat >before.ml <<'ML'
let before=Target.marker
let ret,(empty,(cell,(run,_)))=Target.bundle
let after=Target.marker
ML
cat >mutation.ml <<'ML'
let ()=Target.holder.tuple<-Target.replacement_cell,43
ML
cat >check.ml <<'ML'
let require name condition=if not condition then failwith name
module A(X:module type of Before)=struct end
module B(X:module type of Raw)=struct end
module AB=A(Raw)
module BA=B(Before)
let collect()=Gc.full_major();Gc.full_major()
let ()=
 require "projection only namespace"(Only_raw.first=1&&Only_raw.third=3);
 require "one tuple snapshot across modules"(Only_raw.borrowed_cell==Target.original_cell&&Only_raw.borrowed_count=41&&snd Target.holder.tuple=43);
 require "declaration order values"(Raw.before=17&&Raw.after=17);
 require "exact projected functions and cell"(Raw.ret==Before.ret&&Raw.run==Before.run&&Raw.cell==Before.cell&&Raw.run==Prog.run);
 let (_:bytes list)=Raw.empty and (_:(unit->bytes)list)=Raw.empty in
 let bytes=Bytes.make 4096 'x'and pending,wake=Lwt.task()in
 let owner={Target.cell=Raw.cell;pending;fault=None}in
 require "generic bytes"(match Lwt.state(Raw.ret bytes)with Lwt.Return value->value==bytes|_->false);
 let fn()=bytes in require "generic function"(match Lwt.state(Raw.ret fn)with Lwt.Return value->value==fn|_->false);
 Lwt.with_value Target.key(Some 81)(fun()->require "same promise/context"(Raw.run owner bytes==pending&& !Target.seen=Some 81));
 let fault=Failure "projection"in owner.fault<-Some fault;
 require "original fault"(try ignore(Raw.run owner bytes);false with error->error==fault);owner.fault<-None;
 Lwt.cancel pending;require "original cancellation"(match Lwt.state pending with Lwt.Fail Lwt.Canceled->true|_->false);
 let measure f=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.before in
 let old=measure(fun()->Before.ret 7)and fresh=measure(fun()->Raw.ret 7)in require "exact return allocation"(old=fresh);
 let p=Lwt.return bytes in let owner={owner with Target.pending=p}in
 let a=measure(fun()->Before.run owner bytes)and b=measure(fun()->Raw.run owner bytes)in require "exact call allocation"(a=b);
 let weak=Weak.create 1 in
 let[@inline never] install()=let bytes=Bytes.make 1048576 'w'in Weak.set weak 0(Some bytes);Raw.cell:=Some bytes in
 install();collect();require "live projected cell"(Weak.check weak 0);Before.cell:=None;collect();require "natural release"(not(Weak.check weak 0));
 Printf.printf "PASS: exact tuple projection APIs/objects/generics/promise/context/fault/cancel, declaration order, projection-only namespaces, allocation %.0f/%.0f and %.0f/%.0f B, natural Weak ownership.\n"old fresh a b
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml $(ocamldep -sort soma_published_*.ml) soma_bindings.mli soma_bindings.ml prog.mli prog.ml mutation.ml before.ml raw.ml only_raw.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
python3 - <<'PY'
from pathlib import Path
p=Path('bindings.definition');s=p.read_text().replace('"(ret, (empty, (cell, (run, _))))"','"(ret, (empty, (cell, (run, ignored))))"');p.write_text(s)
PY
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
if cmp -s hash.log changed-hash.log||cmp -s before-abi changed/native_abi.manifest;then echo 'projection shape omitted from fingerprints' >&2;exit 1;fi
cat >main.soma <<'SOMA'
Definition main:=true.
SOMA
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
python3 - <<'PY'
from pathlib import Path
assert not Path('native/native_binding_projections.manifest').exists()
assert not list(Path('native').glob('soma_published_*.ml'))
PY
printf '%s\n' 'PASS: checked generic projection member inference, invalid declarations, provenance/fingerprints and producer cleanup.'
