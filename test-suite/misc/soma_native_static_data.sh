#!/usr/bin/env bash
# Checked Source reduction, not parsing generated ML or executing native reads.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 26 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type data=(string * [ `Raw | `Screen | `Quiet ])list
module type API=sig type t end
let shared:data=["raw",`Raw;"screen",`Screen;"quiet",`Quiet]
type owner={bytes:bytes;pending:bytes Lwt.t;mutable fault:exn option}
let key:int Lwt.key=Lwt.new_key()
let hook=ref(fun (_:data) (_:owner) (_:bytes)->())
let send data owner payload=(!hook)data owner payload;match owner.fault with Some e->raise e|None->owner.pending
let owner_slot:owner Weak.t=Weak.create 1
let consume data owner=let size=Bytes.length owner.bytes+List.length data in
 Gc.full_major();size,Weak.check owner_slot 0
let dynamic()=failwith "static evaluation ran a native callback"
ML
cat >recipes.soma <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String Strings.Ascii.
Import ListNotations.
Local Open Scope string_scope.
Definition recipe {A:Type} (raw screen quiet:A) := [("raw",raw);("screen",screen);("quiet",quiet)].
Definition identity_data {A:Type} (value:A):=value.
Definition binary_text:=String.string_of_list_ascii(map Ascii.ascii_of_nat(seq 0 256)).
Definition details := Some(binary_text,[(true,PrimInt63.sub 0%uint63 1%uint63);(false,4611686018427387904%uint63)]).
Definition empty_recipe(A:Type):list A:= [].
Definition optional_recipe(A:Type):option(A->A):=None.
Definition count_recipe:=List.length[true;false;true].
Definition char_recipe:=Ascii.ascii_of_nat 255.
Definition real_recipe{A:Type}(value:A):=(value,value).
Definition forged:Native.native_handle "target.console":=Native.Native_handle 0.
Definition effect_value:=Native.Export(Native.Return["forbidden"]).
SOMA
cat >target.definition <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String Strings.Ascii.
Import ListNotations.
Import recipes.
Local Open Scope string_scope.
OCaml Native Polymorphic Variant console := ["Raw";"Screen";"Quiet"].
OCaml Native Construct raw : unit -> console := "Raw".
OCaml Native Construct screen : unit -> console := "Screen".
OCaml Native Construct quiet : unit -> console := "Quiet".
OCaml Native Polymorphic Variant boxed (A:Type) := ["Box" : unit;"Fn" : (A->bool)].
OCaml Native Construct box : forall A:Type,unit -> boxed A := "Box".
OCaml Native Static Data boxed_data : forall A:Type,(boxed A * boxed A) := real_recipe With [box].
Local Abbreviation data := (list (string * console))%type.
OCaml Native Static Data shared : data := recipe With [raw;screen;quiet].
OCaml Native Static Data reused : data := identity_data With [shared].
OCaml Native Static Data details_value : option(string * list(bool * PrimInt63.int)) := details.
OCaml Native Static Data empty : forall A:Type,list A := empty_recipe.
OCaml Native Static Data optional : forall A:Type,option(A->A) := optional_recipe.
OCaml Native Static Data count_value : nat := count_recipe.
OCaml Native Static Data char_value : ascii := char_recipe.
OCaml Native External Type real := "float".
OCaml Native Float fraction : real := "1.25".
OCaml Native Static Data real_pair : real*real := real_recipe With [fraction].
OCaml Native External Type owner := "Target.owner".
OCaml Native External Type bytes := "Bytes.t".
OCaml Native External Value prior_data : data := "Target.shared".
OCaml Native External Value send : data -> owner -> bytes -> promise bytes := "Target.send".
OCaml Native Static Apply bound_send : owner -> bytes -> promise bytes := send With [shared] AtFullApplication.
OCaml Native Static Apply prior_send : owner -> bytes -> promise bytes := send With [prior_data] AtFullApplication.
OCaml Native External Value consume : data -> owner -> (PrimInt63.int*bool) := "Target.consume".
OCaml Native Static Apply bound_consume : owner -> (PrimInt63.int*bool) := consume With [shared] AtFullApplication.
OCaml Native Static Apply prior_consume : owner -> (PrimInt63.int*bool) := consume With [prior_data] AtFullApplication.
OCaml Native Static Invoke invoked_send : owner -> bytes -> promise bytes := send With
 [Value shared;Argument 0;Argument 1] AtFullApplication.
OCaml Native Reexport Value exported_data := invoked_send.
OCaml Native External Callback dynamic : unit -> console := "Target.dynamic".
Fail OCaml Native Static Data wrong_result : list string := recipe With [raw;screen;quiet].
Fail OCaml Native Static Data too_few : data := recipe With [raw;screen].
Fail OCaml Native Static Data too_many : data := recipe With [raw;screen;quiet;raw].
Fail OCaml Native Static Data wrong_domain : data := recipe With [fraction;screen;quiet].
Fail OCaml Native Static Data runtime_read : data := recipe With [dynamic;screen;quiet].
Fail OCaml Native Static Data borrowed_read : data := identity_data With [prior_data].
Fail OCaml Native Static Data direct_native : console := raw.
Fail OCaml Native Static Data forged_value : console := forged.
Fail OCaml Native Static Data effect_data : Native.entry(list string) := effect_value.
OCaml Native Static Data specialized_empty : list bool := empty_recipe.
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native.
Import target.
Definition read(_:unit):=Native.Export(Native.Call_callback shared tt).
Definition read_again(_:unit):=Native.Export(Native.Call_callback reused tt).
Definition prior_read(_:unit):=Native.Export(Native.Call_callback prior_data tt).
Definition details:=Native.Export(Native.Call_callback details_value tt).
Definition count:=Native.Export(Native.Call_callback count_value tt).
Definition character:=Native.Export(Native.Call_callback char_value tt).
Definition floats:=Native.Export(Native.Call_callback real_pair tt).
Definition boxes(A:Type):=Native.Export(Native.Call_callback(boxed_data A)tt).
Definition empty_list(A:Type):=Native.Export(Native.Call_callback(empty A)tt).
Definition optional_function(A:Type):=Native.Export(Native.Call_callback(optional A)tt).
Definition factory(_:unit):=Native.Export(Native.Call_callback bound_send tt).
Definition prior_factory(_:unit):=Native.Export(Native.Call_callback prior_send tt).
Definition consume_factory(_:unit):=Native.Export(Native.Call_callback bound_consume tt).
Definition prior_consume_factory(_:unit):=Native.Export(Native.Call_callback prior_consume tt).
Definition invoked:=Native.Export(Native.Call_callback invoked_send tt).
Definition main(A:Type):=(read,read_again,prior_read,details,count,character,floats,boxes A,empty_list A,optional_function A,
 factory,prior_factory,consume_factory,prior_consume_factory,invoked).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'CHECK'
from pathlib import Path
seen=set()
for row in Path('hash.log').read_text().splitlines():
 if '  assumes 'in row:seen.update(row.split('  assumes ',1)[1].split(', '))
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
assert 'static-data' in Path('native/native_abi.manifest').read_text()
text=''.join(file.read_text()for file in Path('native').glob('soma_data_*.ml'))
assert '0x7fffffffffffffff' in text and '0x4000000000000000' in text
import hashlib,shlex
rows=Path('native/native_static_data.manifest').read_text().splitlines()
assert rows[0]=='soma-native-static-data-v1' and len(rows)>1
for row in rows[1:]:
 symbol,source,source_hash,filename,digest=shlex.split(row)
 assert hashlib.sha256(Path(source).read_bytes()).hexdigest()==source_hash
 assert filename.startswith('soma_data_')and Path(filename).name==filename
 assert hashlib.sha256((Path('native')/filename).read_bytes()).hexdigest()==digest
CHECK
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_variant_*.ml native/soma_data_*.ml .
python3 - <<'EXPORTS'
from pathlib import Path
import shlex
rows=[shlex.split(row) for row in Path('native/native_value_reexports.manifest').read_text().splitlines()[1:]]
assert rows
Path('values.ml').write_bytes((Path('native')/rows[0][4]).read_bytes())
EXPORTS
cat >scoped_native.definition <<'SOMA'
From Soma Require Import Native.
From Stdlib Require Import List.
Import recipes.
OCaml Native External Type element := "S.t".
OCaml Native Static Data empty_value : list element := empty_recipe.
SOMA
cat >scoped.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import scoped_native.
Definition values:=Native.Export(Native.Call_callback empty_value tt).
Definition main:=values.
OCaml Native Static Assembly main As "Checked" With [Value "values" := values].
OCaml Native Lexical Scope main Functor "Make" With ["S" : "Target.API"].
SOMA
soma extract scoped.soma -no-soma-prelude -o scoped-native >scoped.log 2>&1
cp scoped-native/scoped.assembly scoped_out.ml
cp scoped-native/soma_data_*.ml .
cat >check.ml <<'ML' 
let require name condition=if not condition then failwith name
let collect()=Gc.full_major();Gc.full_major()
module A=Scoped_out.Make(struct type t=int end)
module B=Scoped_out.Make(struct type t=bytes end)
let ()=
 let (_:int list)=A.values and (_:bytes list)=B.values in
 require "abstract caller types use the same principal empty constant"(A.values=[] && B.values=[]);
 let data=Prog.read()in
 require "checked recipe/order"(data=Target.shared);
 require "one shared literal across repeated reads"(data==Prog.read());
 require "shared data reuse"(data==Prog.read_again());
 let expected=Some(String.init 256 Char.chr,[true,-1;false,min_int])in
 require "binary string and signed native-word boundaries"(Prog.details=expected);
 require "standard constant data"(Prog.count=3 && Prog.character=Char.chr 255 && Prog.floats=(1.25,1.25));
 let a,b=Prog.floats in require "one float input reused by the checked recipe"(a==b);
 require "generic empty bytes list"((Prog.empty_list:bytes list)=[]);
 require "generic empty function list"((Prog.empty_list:(unit->bytes)list)=[]);
 require "generic optional function"((Prog.optional_function:((bytes->bytes)option))=None);
 let a,b=Prog.boxes in require "shared boxed constructor input"(a==b);
 let (_:([ `Box of unit | `Fn of bytes -> bool ] * [ `Box of unit | `Fn of bytes -> bool ]))=Prog.boxes in
 let (_:([ `Box of unit | `Fn of (unit -> bytes) -> bool ] * [ `Box of unit | `Fn of (unit -> bytes) -> bool ]))=Prog.boxes in
 require "closed function factory sharing"((Prog.prior_factory()==Prog.prior_factory())=(Prog.factory()==Prog.factory()));
 let payload=Bytes.make 4096 'p' and bytes=Bytes.make 1048576 'o'in
 let pending,resolver=Lwt.task()in let owner={Target.bytes;pending;fault=None}in
 let calls=ref 0 in
 Target.hook:=(fun values given text->incr calls;
  require "shared literal and original owner/payload"(values==data && given==owner && text==payload);
  require "caller context"(Lwt.get Target.key=Some 41));
 Lwt.with_value Target.key(Some 41)(fun()->
  let partial=Prog.factory()owner in require "quiet partial"(!calls=0);
  require "exact pending"(partial payload==pending && !calls=1);
  require "static invocation uses same constant"(Prog.invoked owner payload==pending);
  require "standalone reexport uses same constant"(Values.exported_data owner payload==pending);
  let fault=Failure "static data call"in owner.fault<-Some fault;
  require "fault identity"(try ignore(partial payload);false with error->error==fault);
  owner.fault<-None);
 Target.hook:=(fun _ _ _->());Lwt.wakeup_later resolver payload;
 require "result identity"(Lwt_main.run pending==payload);
 let canceled,_=Lwt.task()in let other={owner with Target.pending=canceled}in
 require "original cancellation target"(Prog.factory()other payload==canceled);
 Lwt.cancel canceled;require "cancellation"(match Lwt.state canceled with Lwt.Fail Lwt.Canceled->true|_->false);
 let measure call=collect();let before=Gc.allocated_bytes()in
  for _=1 to 10000 do ignore(Sys.opaque_identity(call()))done;Gc.allocated_bytes()-.before in
 let same name before after=let a=measure before and b=measure after in
  Printf.printf "%s %.0f/%.0f B\n%!"name a b;require name(a=b)in
 same "literal read allocation"Prog.prior_read Prog.read;
 same "factory allocation"Prog.prior_factory Prog.factory;
 let old=Prog.prior_factory()and fresh=Prog.factory()in
 same "bound call allocation"(fun()->old owner payload)(fun()->fresh owner payload);
 print_endline "PASS: checked Source literals retain generic types, binary/word data, static sharing, original objects/promises/context/faults/cancellation and exact native/bytecode allocation."
let lifetime factory=
 let invoke()=let bytes=Bytes.make 1048576 'x'in
  let owner={Target.bytes;pending=Lwt.return bytes;fault=None}in
  Weak.set Target.owner_slot 0(Some owner);factory()owner in
 let result=invoke()in collect();result,Weak.check Target.owner_slot 0
let ()=
 let old=lifetime Prog.prior_consume_factory and fresh=lifetime Prog.consume_factory in
 require "consumed owner phases"(old=fresh);
 require "natural owner release"(not(snd fresh));
 print_endline "PASS: closed static-data callbacks preserve natural consumed-owner Weak phases."
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt.unix -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml $(ocamldep -sort soma_variant_*.ml soma_data_*.ml) soma_bindings.ml prog.mli prog.ml values.ml scoped_out.ml check.ml
 ./"check-$compiler"
done
cp target.definition original-definition
cp native/native_abi.manifest original-abi
python3 - <<'CHANGE'
from pathlib import Path
p=Path('recipes.soma');s=p.read_text().replace('("raw",raw);("screen",screen)','("RAW",raw);("screen",screen)',1);p.write_text(s)
CHANGE
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
if cmp -s hash.log changed-hash.log || cmp -s original-abi changed/native_abi.manifest;then
 echo 'changed Source data omitted from semantic/ABI identity' >&2;exit 1
fi
printf '%s\n' 'PASS: typed Source recipe shape/effect/forged-input rejection and semantic/ABI identity.'

# Only unchanged producer-owned constants and manifests may be removed.
python3 - <<'CLEANUP'
from pathlib import Path
files=sorted(Path('native').glob('soma_data_*.ml'))
assert len(files)>1
Path('kept-filename').write_text(files[0].name)
files[0].write_text(files[0].read_text()+'(* caller edit retained *)\n')
Path('kept-bytes').write_bytes(files[0].read_bytes())
CLEANUP
cat >main.soma <<'SOMA'
Definition main := true.
SOMA
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
python3 - <<'CLEANUP'
from pathlib import Path
kept=Path('native')/Path('kept-filename').read_text()
assert kept.read_bytes()==Path('kept-bytes').read_bytes()
assert list(Path('native').glob('soma_data_*.ml'))==[kept]
assert not Path('native/native_static_data.manifest').exists()
CLEANUP
printf '%s\n' 'PASS: obsolete constants/manifests removed while caller-edited data is preserved.'
