#!/usr/bin/env bash
# Borrowed scalar/cell/data publication must retain the provider's exact values.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 25 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type owner={bytes:bytes;fault:exn}
let owner={bytes=Bytes.make 1048576 'x';fault=Failure "borrowed binding"}
let cell:bytes option ref=ref None
let name=Bytes.to_string(Bytes.of_string "borrowed")
let count=17
let other_count=18
let empty=[]
let optional=None
let returned=Lwt.return
let dynamic_target()=failwith "publication ran runtime callback"
let wrong="wrong native type"
ML
cat >target.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native External Value marker : unit := "Stdlib.ignore" With "unused".
SOMA
cat >recipe.soma <<'SOMA'
From Stdlib Require Import List.
Definition empty_data(A:Type):list A:=nil.
SOMA
cat >bindings.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String.
Import recipe.
OCaml Native External Type bytes := "Bytes.t".
OCaml Native External Type owner_type := "Target.owner".
OCaml Native External Value owner_input : owner_type := "Target.owner".
OCaml Native External Value cell_input : reference(option bytes) := "Target.cell".
OCaml Native External Value name_input : string := "Target.name".
OCaml Native External Value count_input : PrimInt63.int := "Target.count".
OCaml Native External Value empty_input : forall A:Type,list A := "Target.empty".
OCaml Native External Value optional_input : forall A:Type,option A := "Target.optional".
OCaml Native External Value ret_input : forall A:Type,A->promise A := "Target.returned".
OCaml Native Static Data staged_input : forall A:Type,list A := recipe.empty_data.
OCaml Native Reexport Binding owner := owner_input.
OCaml Native Reexport Binding cell := cell_input.
OCaml Native Reexport Binding name := name_input.
OCaml Native Reexport Binding count := count_input.
OCaml Native Reexport Binding empty := empty_input.
OCaml Native Reexport Binding optional := optional_input.
OCaml Native Reexport Binding ret := ret_input.
OCaml Native Reexport Binding staged := staged_input.
Fail OCaml Native Reexport Value value_still_rejects_scalar := count_input.
Fail OCaml Native Reexport Binding invalid_source := tt.
OCaml Native External Callback dynamic : unit->PrimInt63.int := "Target.dynamic_target".
Fail OCaml Native Reexport Binding invalid_dynamic := dynamic.
OCaml Native Get bytes_field : owner_type -> bytes := "bytes".
Fail OCaml Native Reexport Binding invalid_field := bytes_field.
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native.
Import target bindings.
Definition main := (owner,cell,name,count,empty,optional,ret,staged,Native.Export(Native.Call_callback marker tt)).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
rows=Path('native/native_value_reexports.manifest').read_text().splitlines()
assert rows[0]=='soma-native-value-reexports-v1'
rows=[shlex.split(row)for row in rows[1:]]
assert [row[6]for row in rows]==['owner','cell','name','count','empty','optional','ret','staged']
assert [row[8]for row in rows]==list(map(str,range(8)))
for symbol,namespace,source,source_hash,file,digest,name,owner,order in rows:
 assert symbol==namespace+'.'+name and hashlib.sha256(Path(source).read_bytes()).hexdigest()==source_hash
 assert Path(file).name==file and hashlib.sha256(Path('native',file).read_bytes()).hexdigest()==digest
Path('raw.ml').write_bytes(Path('native',rows[0][4]).read_bytes())
Path('scope.ml').write_text('include Soma_bindings.'+Path(rows[0][4]).stem.capitalize()+'\n')
assert not any('  assumes 'in row and row.split('  assumes ',1)[1]!='Corelib.Numbers.Cyclic.Int63.PrimInt63.int'for row in Path('hash.log').read_text().splitlines())
PY
(cd native&&dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_bindings.ml,soma_bindings.mli} .
cp native/soma_data_*.ml .
cat >original.ml <<'ML'
let owner=Target.owner
let cell=Target.cell
let name=Target.name
let count=Target.count
let empty=Target.empty
let optional=Target.optional
let ret=Target.returned
let staged=[]
ML
cat >check.ml <<'ML'
let require name condition=if not condition then failwith name
module A(X:module type of Original)=struct end
module B(X:module type of Raw)=struct end
module AB=A(Raw)
module BA=B(Original)
module AS=A(Scope)
let collect()=Gc.full_major();Gc.full_major()
let ()=
 require "same native owner/cell/string"(Raw.owner==Target.owner&&Scope.owner==Target.owner&&Raw.cell==Target.cell&&Scope.cell==Target.cell&&Raw.name==Target.name&&Scope.name==Target.name);
 require "exact scalar"(Raw.count=17&&Scope.count=17);
 let (_:bytes list)=Raw.empty and (_:(unit->bytes)list)=Raw.empty in
 let (_:(bytes->bytes)option)=Raw.optional and (_:bytes option)=Scope.optional in
 let (_:(bytes->bytes)list)=Raw.staged and (_:bytes list)=Scope.staged in
 require "original borrowed function"(Raw.ret==Target.returned&&Scope.ret==Target.returned);
 let payload=Bytes.make 4096 'p'in
 Raw.cell:=Some payload;
 require "shared live mutable cell"(match !(Target.cell),!(Scope.cell)with Some a,Some b->a==payload&&b==payload|_->false);
 require "exact promise payload"(match Lwt.state(Raw.ret payload)with Lwt.Return actual->actual==payload|_->false);
 let callback()=payload in require "generic function"(match Lwt.state(Scope.ret callback)with Lwt.Return actual->actual==callback|_->false);
 let measure f=collect();let start=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.start in
 let old=measure(fun()->Original.ret 7)and fresh=measure(fun()->Raw.ret 7)in
 require "exact public callback allocation"(old=fresh);
 let weak=Weak.create 1 in
 let[@inline never] install()=let bytes=Bytes.make 1048576 'b'in Weak.set weak 0(Some bytes);Raw.cell:=Some bytes in
 install();collect();require "borrowed cell retains current payload"(Weak.check weak 0);
 Scope.cell:=None;collect();require "no payload snapshot"(not(Weak.check weak 0));
 Printf.printf "PASS: native borrowed scalar/cell/data/function bindings retain full public types, generic bytes/functions, exact identities/live mutation/promise payloads/allocation %.0f/%.0f B and natural Weak release.\n"old fresh
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml $(ocamldep -sort soma_data_*.ml) soma_bindings.mli soma_bindings.ml raw.ml scope.ml original.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
python3 - <<'PY'
from pathlib import Path
p=Path('bindings.definition');p.write_text(p.read_text().replace('"Target.count"','"Target.other_count"'))
PY
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
if cmp -s native/native_abi.manifest changed/native_abi.manifest||cmp -s hash.log changed-hash.log;then
 echo 'borrowed binding target missing from semantic/ABI identity' >&2;exit 1
fi
python3 - <<'PY'
from pathlib import Path
p=Path('bindings.definition');p.write_text(p.read_text().replace('"Target.other_count"','"Target.wrong"'))
PY
soma extract main.soma -no-soma-prelude -o invalid >invalid.log 2>&1
if (cd invalid&&dune build --profile release -j2)>invalid-build.log 2>&1;then
 echo 'incorrect native scalar signature compiled' >&2;exit 1
fi
python3 - <<'NATIVE_ERROR'
from pathlib import Path
log=Path('invalid-build.log').read_text()
assert 'Target.wrong'in log and 'expected'in log and 'string'in log and 'int'in log,log
NATIVE_ERROR
printf '%s\n' 'PASS: invalid Source/native boundaries and changed binding fingerprints.'
