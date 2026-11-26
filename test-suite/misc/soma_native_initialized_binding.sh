#!/usr/bin/env bash
# Initialization is once per published owner, shared by getters/raw exports.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 24 "$work"/*.log 2>/dev/null||true;fi;if [ "${KEEP:-0}" = 1 ];then echo "Retained $work";else rm -rf "$work";fi;exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type box={cell:bytes option ref}
let count=ref 0
let phases=ref []
let seed:bytes option ref=ref None
let alternate_seed=seed
let build cell=phases:="box":: !phases;incr count;{cell}
let key:int Lwt.key=Lwt.new_key()
let observe=ref(fun (_:box) (_:bytes)->())
let pending:bytes Lwt.t ref=ref(Lwt.return(Bytes.create 0))
let fault:exn option ref=ref None
let default_limit=Some 23
let seen_limit=ref 0
let run box=phases:="run":: !phases;fun ?(limit=0) payload->seen_limit:=(limit:int);(!observe)box payload;match !fault with Some error->raise error|None-> !pending
let returned=Lwt.return
let empty=[]
let factory values()=values
let read box=phases:="read":: !phases;box.cell
let dynamic()=failwith "runtime getter ran"
let use_float(_ :float)=build seed
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
OCaml Native External Type box_type := "Target.box".
OCaml Native External Value seed : reference(option bytes) := "Target.seed".
OCaml Native External Value build : reference(option bytes)->box_type := "Target.build".
OCaml Native Callable run_type Optional limit := forall(limit:option PrimInt63.int),bytes->promise bytes.
OCaml Native External Value run_leaf : box_type->run_type := "Target.run".
OCaml Native External Value read_leaf : box_type->reference(option bytes) := "Target.read".
OCaml Native External Value returned : forall A:Type,A->promise A := "Target.returned".
OCaml Native Static Initialize box_init : box_type := build With [seed].
OCaml Native Reexport Binding box := box_init.
OCaml Native Published Value box_read : box_type := box.
OCaml Native Static Initialize run_init : run_type := run_leaf With [box_read].
OCaml Native Reexport Binding run := run_init.
OCaml Native Published Value run_read : run_type := run.
OCaml Native Static Initialize cell_init : reference(option bytes) := read_leaf With [box_read].
OCaml Native Reexport Binding cell := cell_init.
OCaml Native Reexport Binding ret := returned.
OCaml Native Published Value ret_read : forall A:Type,A->promise A := ret.
Fail OCaml Native Published Value wrong_generic : forall A B:Type,A->promise B := ret.
OCaml Native External Value empty_value : forall A:Type,list A := "Target.empty".
OCaml Native External Value factory_value : forall A:Type,list A->unit->list A := "Target.factory".
OCaml Native Static Initialize generic_init : forall A:Type,unit->list A := factory_value With [empty_value].
OCaml Native Reexport Binding generic_factory := generic_init.
OCaml Native External Value default_value : option PrimInt63.int := "Target.default_limit".
OCaml Native Static Initialize selected_init : bytes->promise bytes := run_read With [default_value].
OCaml Native Reexport Binding selected := selected_init.
Fail OCaml Native Published Value wrong_source : box_type := seed.
Fail OCaml Native Published Value wrong_type : bytes := box.
Fail OCaml Native Static Initialize wrong_domain : box_type := build With [box_read].
Fail OCaml Native Static Initialize wrong_result : bytes := build With [seed].
Fail OCaml Native Static Initialize wrong_arity : box_type := build With [seed;seed].
OCaml Native External Type real := "float".
OCaml Native Float inline_float : real := "1.25".
OCaml Native External Value float_target : real->box_type := "Target.use_float".
Fail OCaml Native Static Initialize invalid_literal : box_type := float_target With [inline_float].
OCaml Native External Callback dynamic : unit->box_type := "Target.dynamic".
Fail OCaml Native Static Initialize wrong_dynamic : box_type := dynamic With [seed].
SOMA
cat >bridge.definition <<'SOMA'
From Soma Require Import Native Handles.
Import bindings.
OCaml Native Published Value origin : box_type := bindings.box.
OCaml Native Reexport Binding same := origin.
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native.
Import target bindings bridge.
Definition read_box := Native.Export(Native.Call_callback box_read tt).
Definition read_run := Native.Export(Native.Call_callback run_read tt).
Definition main := (box,run,cell,ret,generic_factory,selected,same,read_box,read_run,Native.Export(Native.Call_callback marker tt)).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
for file,header,width in [('native_binding_initializers.manifest','soma-native-binding-initializers-v1',5),('native_value_reexports.manifest','soma-native-value-reexports-v1',9)]:
 lines=Path('native',file).read_text().splitlines();assert lines[0]==header
 for line in lines[1:]:
  row=shlex.split(line);assert len(row)==width
  namespace,source,digest,output,generated=row if width==5 else row[1:6]
  assert hashlib.sha256(Path(source).read_bytes()).hexdigest()==digest
  assert hashlib.sha256(Path('native',output).read_bytes()).hexdigest()==generated
  if width==9:Path('raw.ml'if namespace=='bindings'else'bridge_raw.ml').write_bytes(Path('native',output).read_bytes())
assert len(list(Path('native').glob('soma_published_*.ml')))==2
assert all('  assumes 'not in line or line.split('  assumes ',1)[1]=='Corelib.Numbers.Cyclic.Int63.PrimInt63.int'for line in Path('hash.log').read_text().splitlines())
PY
(cd native&&dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_bindings.ml,soma_bindings.mli,prog.ml,prog.mli} .
cp native/soma_published_*.ml native/soma_callable_*.ml .
cat >check.ml <<'ML'
let require name condition=if not condition then failwith name
module Original()=struct
 let box=Target.build Target.seed
 let run=Target.run box
 let cell=Target.read box
 let ret=Target.returned
end
let collect()=Gc.full_major();Gc.full_major()
let ()=
 require "one initialized owner across raw exports, bindings and Source getters"(!Target.count=1&&Raw.box==Prog.read_box&&Bridge_raw.same==Raw.box&&Raw.run==Prog.read_run&&Raw.cell==Target.seed);
 require "ordered one-time initialization"(!Target.phases=["read";"run";"box"]);
 let module Old=Original()in require "independent oracle initialized once"(!Target.count=2);
 require "same ordered initializer effects"(!Target.phases=["read";"run";"box";"read";"run";"box"]);
 let payload=Bytes.make 4096 'p'and promise,wake=Lwt.task()in Target.pending:=promise;
 Target.observe:=(fun box bytes->require "original initialized owner and payload"(box==Raw.box&&bytes==payload);require "caller context"(Lwt.get Target.key=Some 71));
 Lwt.with_value Target.key(Some 71)(fun()->
  let partial=Raw.run ~limit:7 in
  require "quiet partial/no reinitialization"(!Target.count=2);
  require "exact pending"(partial payload==promise);
  require "published callable optional prefix"(Raw.selected payload==promise&& !Target.seen_limit=23);
  let fault=Failure "published fault"in Target.fault:=Some fault;
  require "same exception"(try ignore(partial payload);false with error->error==fault);
  Target.fault:=None);
 Target.observe:=(fun _ _->());Lwt.wakeup_later wake payload;
 require "exact generic payload"(match Lwt.state(Raw.ret payload)with Lwt.Return value->value==payload|_->false);
 let (_:bytes list)=Raw.generic_factory()and (_:(unit->bytes)list)=Raw.generic_factory()in
 require "generic published borrow retains original function"
   (Soma_bindings.soma_native_62696e64696e6773_7265745f72656164()==Raw.ret);
 let fn()=payload in require "generic function"(match Lwt.state(Raw.ret fn)with Lwt.Return value->value==fn|_->false);
 let pending,_=Lwt.task()in Target.pending:=pending;require "same cancellation target"(Raw.run payload==pending);
 Lwt.cancel pending;require "original canceled"(match Lwt.state pending with Lwt.Fail Lwt.Canceled->true|_->false);
 Target.pending:=Lwt.return payload;
 let measure f=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.before in
 let before=measure(fun()->Old.run payload)and after=measure(fun()->Raw.run payload)in
 require "exact public call allocation"(before=after);
 let weak=Weak.create 1 in
 let[@inline never] install()=let bytes=Bytes.make 1048576 'w'in Weak.set weak 0(Some bytes);Raw.cell:=Some bytes in
 install();collect();require "live original cell"(Weak.check weak 0);
 Target.seed:=None;collect();require "natural release without payload snapshot"(not(Weak.check weak 0));
 Printf.printf "PASS: one initialized publication across raw exports, Source getters and namespaces; original owner/cell/function/payload identities, labels/generics, context/promise/fault/cancellation and exact allocation %.0f/%.0f B, natural Weak release.\n"before after
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml $(ocamldep -sort soma_published_*.ml soma_callable_*.ml) soma_bindings.mli soma_bindings.ml prog.mli prog.ml raw.ml bridge_raw.ml check.ml
 ./"check-$compiler"
done
python3 - <<'PY'
from pathlib import Path
p=Path('bindings.definition');p.write_text(p.read_text().replace('"Target.seed"','"Target.alternate_seed"'))
PY
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
if cmp -s hash.log changed-hash.log||cmp -s native/native_abi.manifest changed/native_abi.manifest;then echo 'initialization dependency omitted from semantic/ABI identity' >&2;exit 1;fi
cat >main.soma <<'SOMA'
Definition main:=true.
SOMA
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
python3 - <<'CLEANUP'
from pathlib import Path
assert not Path('native/native_binding_initializers.manifest').exists()
assert not list(Path('native').glob('soma_published_*.ml'))
assert not Path('native/native_value_reexports.manifest').exists()
assert not list(Path('native').glob('soma_values_*.exports'))
CLEANUP
printf '%s\n' 'PASS: typed initialization/references, authenticated products, semantic identity and producer cleanup.'
