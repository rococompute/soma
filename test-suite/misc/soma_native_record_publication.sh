#!/usr/bin/env bash
# Full checked record patterns publish original members without retaining owners.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 30 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type ('a,'b) bundle={ret:'a->'a Lwt.t;empty:'b list;cell:bytes option ref}
let cell=ref None
let shared={ret=Lwt.return;empty=[];cell}
type prepared={first:string->bytes Lwt.t;second:string->bytes}
let weak=Weak.create 1
let prepares=ref 0
let calls=ref 0
let key:int Lwt.key=Lwt.new_key()
let seen=ref None
let failure=Failure "record publication"
let broken=ref false
let response=ref(Lwt.return(Bytes.create 0))
let inspect=ref(fun (_:bytes)->())
let unit=()
let make()=
 incr prepares;let owner=Bytes.make 1048576 'o'in Weak.set weak 0(Some owner);
 let first _=incr calls;seen:=Lwt.get key;(!inspect)owner;if !broken then raise failure;!response in
 let second text=Bytes.of_string text in {first;second}
ML
cat >target.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native External Value marker : unit := "Target.unit".
SOMA
cat >producer.soma <<'SOMA' 
From Soma Require Import Native Handles.
From Stdlib Require Import List Strings.String.
Record bundle(A B:Type):={ret:A->promise A;empty:list B;cell:reference(option buffer)}.
Record prepared:={first:string->promise buffer;second:string->buffer}.
Record dependent:={shape:Type;value:shape}.
Definition main:=tt.
SOMA
cat >pub.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import List Strings.String.
Import producer.
OCaml Native Record Alias bundle := producer.bundle As "Target.bundle".
OCaml Native Record Alias prepared := producer.prepared As "Target.prepared".
Fail OCaml Native Record Alias dependent := producer.dependent As "Target.dependent".
OCaml Native External Value shared_value : forall A B:Type,bundle A B := "Target.shared".
Fail OCaml Native Reexport Projection missing := shared_value As "{ Target.ret; empty }".
Fail OCaml Native Reexport Projection wrong_owner := shared_value As "{ Other.ret; empty; cell }".
Fail OCaml Native Reexport Projection duplicate := shared_value As "{ Target.ret; ret; cell }".
Fail OCaml Native Reexport Projection injected := shared_value As "{ Target.ret; empty; cell } in failwith".
OCaml Native External Callback dynamic : unit->prepared := "Target.make".
Fail OCaml Native Reexport Projection runtime := dynamic As "{ Target.first; second }".
OCaml Native Reexport Projection shared := shared_value As "{ Target.ret; empty; cell }".
OCaml Native Projected Value ret_value : forall A:Type,A->promise A := shared Member "ret".
OCaml Native Projected Value empty_value : forall B:Type,list B := shared Member "empty".
Fail OCaml Native Projected Value wrong_type : buffer := shared Member "ret".
Fail OCaml Native Reexport Binding cell := shared_value.
OCaml Native External Value unit_value : unit := "Target.unit".
OCaml Native External Value make : unit->prepared := "Target.make".
OCaml Native Static Initialize Expression initialized : prepared := Call make [Value unit_value].
OCaml Native Reexport Projection members := initialized As "{ Target.first; second }".
OCaml Native Projected Value first_value : string->promise buffer := members Member "first".
SOMA
cat >concrete.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import List Strings.String.
Import pub.
OCaml Native External Value original : bundle buffer bool := "Target.shared".
OCaml Native Reexport Projection members := original As "{ Target.ret; empty; cell }".
OCaml Native Projected Value read_ret : buffer->promise buffer := members Member "ret".
Fail OCaml Native Projected Value wrong_concrete : string->promise string := members Member "ret".
Fail OCaml Native Projected Value wrong_empty : list buffer := members Member "empty".
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native.
Import pub concrete target.
Definition main:=(pub.shared,pub.members,ret_value,empty_value,first_value,concrete.members,Native.Export(Native.Call_callback target.marker tt)).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
rows=[shlex.split(l)for l in Path('native/native_binding_projections.manifest').read_text().splitlines()[1:]]
assert sorted((r[1],r[6],r[8])for r in rows)==[('concrete','ret,empty,cell','0'),('pub','first,second','1'),('pub','ret,empty,cell','0')]
for _,_,src,digest,filename,expected,*_ in rows:
 assert hashlib.sha256(Path(src).read_bytes()).hexdigest()==digest
 assert hashlib.sha256(Path('native',filename).read_bytes()).hexdigest()==expected
initializers=[shlex.split(l)for l in Path('native/native_binding_initializers.manifest').read_text().splitlines()[1:]]
assert len(initializers)==2
canonical=next(r[3]for r in initializers if r[0]=='pub')
concrete=next(r[3]for r in initializers if r[0]=='concrete')
Path('concrete.ml').write_bytes(Path('native',concrete).read_bytes())
code=Path('native',canonical).read_text();assert code.count('Target.make')==1
assert 'let { Target.first; second } = ('in code
Path('fresh.ml').write_text('module Make()=struct\n'+code+'\nend\n')
for line in Path('hash.log').read_text().splitlines():
 assumptions=set(line.split('  assumes ',1)[1].split(', '))if'  assumes 'in line else set()
 assert assumptions<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},assumptions
PY
cp target.ml native/target.ml
(cd native&&dune build --profile release -j2)>native-build.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cat >old.ml <<'ML'
module Make()=struct
 let {Target.ret;empty;cell}=Target.shared
 let {Target.first;second}=Target.make()
end
ML
cat >concrete_before.ml <<'ML'
let {Target.ret;empty;cell}=(Target.shared : (bytes,bool) Target.bundle)
ML
cat >check.ml <<'ML' 
module C(X:module type of Concrete_before)=struct end
module D(X:module type of Concrete)=struct end
module CD=C(Concrete)
module DC=D(Concrete_before)
module Before=Old.Make()
module After=Fresh.Make()
module A(X:module type of Before)=struct end
module B(X:module type of After)=struct end
module AB=A(After)
module BA=B(Before)
let require label ok=if not ok then failwith label
let[@inline never] allocation f=Gc.full_major();let start=Gc.allocated_bytes()in
 for _=1 to 1000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.start
let window use create=
 let kept=ref None in let[@inline never] start()=kept:=Some(create())in
 start();Gc.full_major();Gc.full_major();let alive=Weak.check Target.weak 0 in
 (match !kept with Some value->use value|None->assert false);
 kept:=None;Gc.full_major();Gc.full_major();alive,Weak.check Target.weak 0
let ()=
 require "exact one initializer"(!Target.prepares=2&& !Target.calls=0);
 require "shared objects"(Before.ret==After.ret&&Before.cell==After.cell&&After.cell==Target.cell);
 let bytes=Bytes.make 4096 'b'in require "generic bytes"(Lwt_main.run(After.ret bytes)==bytes);
 let fn x=x in require "generic function"(Lwt_main.run(After.ret fn)==fn);
 let (_:bytes list)=After.empty and (_:(unit->bytes)list)=After.empty in
 let pending,wake=Lwt.task()in Target.response:=pending;
 Target.inspect:=(fun owner->require "owner"(Bytes.length owner=1048576));
 require "promise/context"(Lwt.with_value Target.key(Some 17)(fun()->After.first "call")==pending&& !Target.seen=Some 17);
 Lwt.wakeup wake bytes;require "result"(Lwt_main.run pending==bytes);
 Target.broken:=true;require "fault identity"(try ignore(After.first "fault");false with e->e==Target.failure);
 Target.broken:=false;Target.inspect:=(fun _->());
 let pending,_=Lwt.task()in Target.response:=pending;let result=After.first "cancel"in Lwt.cancel result;
 require "cancellation"(result==pending&&Lwt.state pending=Lwt.Fail Lwt.Canceled);
 Target.response:=Lwt.return bytes;
 let a=allocation(fun()->Before.first "call")and b=allocation(fun()->After.first "call")in require "exact call allocation"(a=b);
 let c=allocation(fun()->let module M=Old.Make()in M.second)and d=allocation(fun()->let module M=Fresh.Make()in M.second)in
 require "exact initialization allocation"(c=d);
 let old=window (fun f->ignore(f "held"))(fun()->let module M=Old.Make()in M.first)and fresh=window (fun f->ignore(f "held"))(fun()->let module M=Fresh.Make()in M.first)in
 require "first retains only original owner"(old=fresh&&fst old&&not(snd old));
 let old=window (fun f->ignore(f "held"))(fun()->let module M=Old.Make()in M.second)and fresh=window (fun f->ignore(f "held"))(fun()->let module M=Fresh.Make()in M.second)in
 require "second does not retain discarded record"(old=fresh&&not(fst old)&&not(snd old));
 Printf.printf "PASS: full record projection API, generic parameters/members, original objects/promise/context/fault/cancel, exact allocation call %.0f/%.0f B init %.0f/%.0f B and natural separate-member Weak lifetimes.\n"a b c d
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt.unix -linkpkg -w -a uint63.ml soma_nat.ml soma_word64.ml soma_handles.ml soma_effect.ml float64.ml target.ml concrete_before.ml concrete.ml old.ml fresh.ml check.ml -o check >"$compiler.log" 2>&1
 ./check
done
cp hash.log before-hash
cp native/native_abi.manifest before-abi
python3 - <<'PY'
from pathlib import Path
p=Path('pub.definition');p.write_text(p.read_text().replace('Projection shared := shared_value As "{ Target.ret; empty; cell }"','Projection shared := shared_value As "{ Target.cell; ret; empty }"'))
PY
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
if cmp -s before-hash changed-hash.log||cmp -s before-abi changed/native_abi.manifest;then echo 'record projection order omitted from identity' >&2;exit 1;fi
printf 'Definition main:=true.\n' >main.soma
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
test ! -e native/native_binding_projections.manifest
python3 - <<'PYCLEAN'
from pathlib import Path
assert not list(Path('native').glob('soma_published_*.ml'))
PYCLEAN
printf 'PASS: invalid shapes/owners/types/dependencies, record member inference, provenance/ABI/order sensitivity and stale output cleanup.\n'
