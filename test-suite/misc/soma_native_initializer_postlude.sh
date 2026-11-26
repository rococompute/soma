#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 25 "$work"/*.log 2>/dev/null||true;fi;if [ "${KEEP:-0}" = 1 ];then echo "Retained $work";else rm -rf "$work";fi;exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
let events=ref []
let phase=ref None
let error=Failure "initializer"
let note name=events:=name:: !events;if !phase=Some name then raise error
let key:int Lwt.key=Lwt.new_key()
let seen=ref None
let pending,wake : bytes Lwt.t * bytes Lwt.u =Lwt.task()
let weak=Weak.create 2
let count=ref 0
let prepare()=note"prepare";let token=Bytes.make 1048576 'w'in
 let slot= !count mod 2 in incr count;Weak.set weak slot(Some token);
 fun (bytes:bytes)->ignore(Sys.opaque_identity token);seen:=Lwt.get key;ignore(Sys.opaque_identity bytes);pending
let finish label fn=note label;fn
let combine left right=note"combine";left,right
let labelled() ?(enabled=true) (bytes:bytes)=if not enabled then raise error;ignore(Sys.opaque_identity bytes);pending
ML
# Tuple annotations cannot be attached directly to an unparenthesized pattern.
python3 - <<'PY'
from pathlib import Path
p=Path('target.ml');p.write_text(p.read_text().replace('let pending,wake :','let (pending,wake) :'))
PY
cat >data.soma <<'SOMA'
From Stdlib Require Import Strings.String.
Local Open Scope string_scope.
Definition unit_value:=tt.
Definition left_label:="left".
Definition right_label:="right".
SOMA
cat >core.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native Constructor failed : string->exception_value := "Failed" 1.
SOMA
cat >pub.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
Import data.
OCaml Native Static Data unit_input : unit := unit_value.
OCaml Native Static Data left_input : string := left_label.
OCaml Native Static Data right_input : string := right_label.
OCaml Native External Value prepare : unit->buffer->promise buffer := "Target.prepare".
OCaml Native External Value finish : string->(buffer->promise buffer)->buffer->promise buffer := "Target.finish".
OCaml Native External Value combine : (buffer->promise buffer)->(buffer->promise buffer)->((buffer->promise buffer)*(buffer->promise buffer)) := "Target.combine".
OCaml Native Static Initialize Expression pair : (buffer->promise buffer)*(buffer->promise buffer) := Call combine [Call finish [Value left_input;Call prepare [Value unit_input]];Call finish [Value right_input;Call prepare [Value unit_input]]].
OCaml Native Reexport Projection members := pair As "(left, right)".
OCaml Native External Value identity_value : forall A:Type,A->A := "Checked.identity".
OCaml Native Reexport Binding identity := identity_value.
OCaml Native External Value failure_value : string->exception_value := "Checked.failure".
OCaml Native Reexport Binding failure := failure_value.
OCaml Native Callable labelled Optional enabled := unit->forall(enabled:option bool),buffer->promise buffer.
OCaml Native External Value labelled_value : labelled := "Target.labelled".
OCaml Native Callable ready_schema Optional enabled := forall(enabled:option bool),buffer->promise buffer.
OCaml Native Static Initialize Expression ready_init : ready_schema := Call labelled_value [Value unit_input].
OCaml Native Reexport Binding ready := ready_init.
Fail OCaml Native Static Initialize Expression wrong : string := Call prepare [Value unit_input].
Fail OCaml Native Static Initialize Expression wrong : promise buffer := Call prepare [Value left_input].
Fail OCaml Native Static Initialize Expression wrong : ready_schema := Call labelled_value [Value left_input].
Fail OCaml Native Static Initialize Expression wrong : ready_schema := Argument 0.
Fail OCaml Native Static Initialize Expression wrong : ready_schema := Call prepare [Value unit_input;Value unit_input;Value unit_input].
OCaml Native External Callback dynamic : unit->buffer := "Bytes.empty".
Fail OCaml Native Static Initialize Expression wrong : buffer := Value dynamic.
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native Handles OCaml.
From Stdlib Require Import Strings.String.
Import pub core.
Definition identity{A:Type}(value:A):=value.
Definition failure message:=Native.Export(Native.Call_callback failed message).
Definition main:=let _ := (pub.members,pub.identity,pub.failure,pub.ready)in (@identity,failure).
Fail OCaml Native Static Postlude main With [Values pub.ready].
OCaml Native Static Assembly main As "Checked" With [Exception "Failed" := failed].
Fail OCaml Native Static Postlude main With [Modules pub.ready].
Fail OCaml Native Static Postlude main With [Values pub.ready;Values pub.members].
OCaml Native Static Postlude main With [Values pub.ready].
Fail OCaml Native Static Postlude main With [Values pub.ready].
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import shlex,hashlib
row=shlex.split(Path('native/native_assemblies.manifest').read_text().splitlines()[1]);assert len(row)==10
_,source,digest,file,product,program,interface,bindings,layout,contract=row
for path,expected in[(source,digest),('native/'+file,product),('native/prog.ml',program),('native/prog.mli',interface),('native/soma_bindings.ml',bindings)]:assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==expected
assert all('  assumes 'not in line or line.split('  assumes ',1)[1]=='Corelib.Numbers.Cyclic.Int63.PrimInt63.int'for line in Path('hash.log').read_text().splitlines())
Path('after.ml').write_text('module Make()=struct\n'+Path('native/main.assembly').read_text()+'\nend\n')
Path('before.ml').write_text('''module Make()=struct
exception Failed of string
module Checked:sig\n'''+Path('native/prog.mli').read_text()+'''\nend=struct
module Soma_bindings=struct
module Soma_handles=struct include Soma_handles exception Failed=Failed end
'''+Path('native/soma_bindings.ml').read_text()+'''\nend\n'''+Path('native/prog.ml').read_text()+'''\nend
let left,right=Target.combine(Target.finish "left"(Target.prepare()))(Target.finish "right"(Target.prepare()))
let identity=Checked.identity
let failure=Checked.failure
let ready=Target.labelled()
end
''')
assert 'native-static-postlude-v1'in Path('native/native_abi.manifest').read_text()
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cp native/soma_data_*.ml .
cp native/soma_callable_*.ml .
cat >check.ml <<'ML'
let require name ok=if not ok then failwith name
let collect()=Gc.full_major();Gc.full_major()
module A(X:module type of Before)=struct end
module B(X:module type of After)=struct end
module AB=A(After)
module BA=B(Before)
let ()=
 Target.events:=[];let module Old=Before.Make()in let trace=List.rev !Target.events in
 Target.events:=[];let module Fresh=After.Make()in
 require "nested right-to-left evaluation and single call sites"(trace=["prepare";"right";"prepare";"left";"combine"]&&trace=List.rev !Target.events);
 require "root exception slot"(Printexc.exn_slot_name(Fresh.failure "x")=Printexc.exn_slot_name(Fresh.Failed "x"));
 require "exception/callback ownership"(match Fresh.failure "x"with Fresh.Failed "x"->true|_->false);
 require "generic bytes and function aliases"(let bytes=Bytes.make 4096 'p'in let fn()=bytes in Fresh.identity bytes==bytes&&Fresh.identity fn==fn);
 let bytes=Bytes.make 4096 'p'in
 Lwt.with_value Target.key(Some 41)(fun()->require "original promise and caller context"(Fresh.left bytes==Target.pending&& !Target.seen=Some 41));
 require "optional residual labels"(Fresh.ready bytes==Target.pending&&Old.ready ~enabled:true bytes==Target.pending);
 require "original optional fault"(try ignore(Fresh.ready ~enabled:false bytes);false with error->error==Target.error);
 let measure f=collect();let start=Gc.allocated_bytes()in for _=1 to 1000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.start in
 let a=measure(fun()->Old.left bytes)and b=measure(fun()->Fresh.left bytes)in require "exact call allocation"(a=b);
 List.iter(fun phase->Target.phase:=Some phase;Target.events:=[];
  let old=try let module M=Before.Make()in ignore M.ready;None with error->Some error in let trace=List.rev !Target.events in
  Target.events:=[];let fresh=try let module M=After.Make()in ignore M.ready;None with error->Some error in
  require("initialization fault:"^phase)(Option.exists((==)Target.error)old&&Option.exists((==)Target.error)fresh&&trace=List.rev !Target.events))["prepare";"right";"left";"combine"];
 Target.phase:=None;
 let held=ref None in
 let[@inline never] before()=Target.count:=0;let module M=Before.Make()in held:=Some M.left in
 let[@inline never] after()=Target.count:=0;let module M=After.Make()in held:=Some M.left in
 List.iter(fun install->install();collect();require "only original left owner retained"(not(Weak.check Target.weak 0)&&Weak.check Target.weak 1);held:=None;collect();require "natural owner release"(not(Weak.check Target.weak 1)))[before;after];
 Lwt.cancel Target.pending;require "original cancellation"(match Lwt.state Target.pending with Lwt.Fail Lwt.Canceled->true|_->false);
 Printf.printf"PASS: complete postlude API, root exception identity, independent generics, nested order/single evaluation, optional residual labels, promise/context/fault/cancel, exact allocation %.0f/%.0f B and natural Weak ownership.\n"a b
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_data_*.ml soma_callable_*.ml before.ml after.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
python3 - <<'PY2'
from pathlib import Path
p=Path('pub.definition');s=p.read_text().replace('Value left_input;Call prepare','Value right_input;Call prepare',1);p.write_text(s)
PY2
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
if cmp -s hash.log changed-hash.log||cmp -s before-abi changed/native_abi.manifest;then echo 'nested initializer omitted from fingerprints' >&2;exit 1;fi
python3 - <<'PY2'
from pathlib import Path
p=Path('pub.definition');s=p.read_text().replace('Binding ready :=','Binding prepared :=');p.write_text(s)
p=Path('main.soma');p.write_text(p.read_text().replace('pub.ready','pub.prepared'))
PY2
soma hash main.soma -no-soma-prelude >scope-hash.log
if cmp -s changed-hash.log scope-hash.log;then echo 'postlude scope omitted from identity' >&2;exit 1;fi
cat >main.soma <<'SOMA'
Definition main:=true.
SOMA
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
python3 - <<'PY2'
from pathlib import Path
assert not Path('native/native_assemblies.manifest').exists()
assert not Path('native/main.assembly').exists()
assert not list(Path('native').glob('soma_published_*.ml'))
PY2
printf '%s\n' 'PASS: typed nested calls, postlude provenance/assumptions/invalid declarations, semantic/ABI identities and cleanup.'

