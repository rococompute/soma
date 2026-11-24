#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?;if [ "$rc" != 0 ];then tail -n 55 "$WORK"/*.log 2>/dev/null||true;fi;rm -rf "$WORK"' EXIT
ocaml(){ opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@" || return $?; }
mkdir "$WORK/app"
cp "$HERE"/examples/example_projects/native_parametric_variants/* "$WORK/app/"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
python3 - "$WORK" <<'PY'
from pathlib import Path
import hashlib,shlex,sys
w=Path(sys.argv[1]);out=w/'native';rows=[shlex.split(s)for s in(out/'native_variants.manifest').read_text().splitlines()[1:]]
assert len(rows)==3
seen=set()
for line in(w/'hash').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
for symbol,source,digest,name,product in rows:
 assert hashlib.sha256((w/'app'/source).read_bytes()).hexdigest()==digest
 assert hashlib.sha256((out/name).read_bytes()).hexdigest()==product
 assert 'Obj.'not in(out/name).read_text()
 module=Path(name).stem;module=module[:1].upper()+module[1:]
 (out/(symbol.rsplit('.',1)[1]+'-module')).write_text(module)
assert 'native-parametric-polyvariant'in(out/'native_abi.manifest').read_text()
assert 'Obj.'not in(out/'soma_bindings.ml').read_text()
PY
cat > "$WORK/native/probe.ml" <<'ML'
module Event=EVENT_MODULE
module Channel=CHANNEL_MODULE
let ensure label condition=if not condition then failwith label
let raw=function `Value value->Ok value|`Closed->Error(Ok())|`Interrupted->Error(Error(Ok()))|`Timeout->Error(Error(Error()))
let shape a b=let a=Obj.repr a and b=Obj.repr b in
 Obj.is_int a=Obj.is_int b && if Obj.is_int a then a=b else
 Obj.tag a=Obj.tag b&&Obj.size a=Obj.size b&&Obj.field a 0=Obj.field b 0&&Obj.field a 1==Obj.field b 1
let ()=
 let text=Bytes.to_string(Bytes.make 1009 'p')and node=ref 17 and array=[|"borrowed"|]in
 let a:string Event.t=Prog.value text and b:int ref Event.t=Prog.value node and c:string array Event.t=Prog.value array in
 ensure"generic Value layout"(shape a(`Value text)&&shape b(`Value node)&&shape c(`Value array));
 ensure"string alias"(match Prog.inspect a with Ok value->value==text|_->false);
 ensure"reference alias"(match Prog.inspect b with Ok value->value==node|_->false);
 ensure"array alias"(match Prog.inspect c with Ok value->value==array|_->false);
 node:=71;array.(0)<-"changed";
 ensure"live reference/array payloads"(match Prog.inspect b,Prog.inspect c with Ok n,Ok a-> !n=71&&a.(0)="changed"|_->false);
 List.iter(fun value->ensure"frozen generic dispatch"(raw value=Prog.inspect value))[a;Prog.closed();Prog.interrupted();Prog.timeout()];
 ensure"concrete instance view"(Prog.inspect_bool(`Value true)=Ok true);
 let pending,wake=Lwt.task()and key=Lwt.new_key()in
 let callback()=ensure"function type-argument context"(Lwt.get key=Some 17);pending in
 let value=Prog.value callback in
 let found=match Prog.inspect_function value with Ok fn->fn|_->assert false in
 ensure"function type-argument alias"(found==callback);
 let answer=Lwt.with_value key(Some 17)found in ensure"promise alias"(answer==pending);Lwt.wakeup wake text;
 ensure"function payload result"(match Lwt.state answer with Lwt.Return value->value==text|_->false);
 let left:(int ref,bytes)Channel.t=Prog.left node and right:(int ref,bytes)Channel.t=Prog.right(Bytes.of_string"right")in
 ensure"two parameter left"(match Prog.channel_view left with Ok value->value==node|_->false);
 ensure"two parameter right"(match Prog.channel_view right,right with Error(Ok value),`Right original->value==original|_->false);
 let pending,wake=Lwt.task()in
 let fn argument=ensure"generic callback argument"(argument==node);ensure"generic callback context"(Lwt.get key=Some 23);pending in
 let value=Prog.apply fn in
 let found=match Prog.channel_view value with Error(Error(Ok fn))->fn|_->assert false in
 ensure"generic callback identity"(found==fn);
 let answer=Lwt.with_value key(Some 23)(fun()->found node)in ensure"generic callback promise identity"(answer==pending);
 let bytes=Bytes.create 1009 in Lwt.wakeup wake bytes;ensure"generic callback result identity"(match Lwt.state answer with Lwt.Return value->value==bytes|_->false);
 ensure"unit/nullary layout"(shape(Prog.unit_case())(`Unit())&&shape(Prog.empty())`Empty);
 ensure"nested schema borrowed payload"(match Prog.nested_view(Prog.nest a)with Ok value->value==a|_->false);
 ensure"generic external callback"(Prog.echo a==a&&Prog.echo b==b);
 let pair=ref 17,Bytes.create 1009 in ensure"product argument"(match Prog.inspect(Prog.value pair)with Ok found->found==pair|_->false);
 let mutable_case:(string,string)Channel.t=Prog.left text in Obj.set_field(Obj.repr mutable_case)0(Obj.field(Obj.repr(`Right text))0);
 ensure"valid live tag update"(match Prog.channel_view mutable_case with Error(Ok value)->value==text|_->false);
 let lifetime view=
  let weak=Weak.create 1 in
  let[@inline never] start()=let parent=`Value(Bytes.to_string(Bytes.make 1013 'p'))in Weak.set weak 0(Some parent);view parent in
  let value=start()in Gc.full_major();Gc.full_major();let alive=Weak.check weak 0 in ignore(Sys.opaque_identity value);alive in
 ensure"consumed generic parent lifetime"(lifetime raw=lifetime Prog.inspect);
 print_endline"PASS: generic native variants: one/two/arrow/product/nested parameters, frozen layouts, mutable aliases, callback/promise identities, context, valid tag updates and consumed-parent Weak lifetimes"
ML
python3 - "$WORK/native" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);f=p/'probe.ml';f.write_text(f.read_text().replace('EVENT_MODULE',(p/'event-module').read_text()).replace('CHANNEL_MODULE',(p/'channel-module').read_text()))
mods=sorted(f.stem for f in p.glob('*.ml')if f.stem!='soma_main')
(p/'dune').write_text('(executable (name probe) (modes exe byte) (modules '+' '.join(mods)+') (libraries lwt) (flags (:standard -w -a)))\n')
PY
ocaml dune build --root "$WORK/native" --profile release -j2 probe.exe probe.bc > "$WORK/build.log" 2>&1
ocaml "$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"
# Identical source schemas in different consumers must keep byte-identical ABI.
mkdir "$WORK/second"
cp "$WORK/app/protocol.definition" "$WORK/second/"
printf 'From Soma Require Native.\nImport protocol.\nDefinition main:=@protocol.inspect.\n' > "$WORK/second/main.soma"
"$SOMA" extract "$WORK/second/main.soma" -o "$WORK/other" > "$WORK/other.log" 2>&1
python3 - "$WORK" <<'PY'
from pathlib import Path
import sys
w=Path(sys.argv[1]);a={p.name:p.read_bytes()for p in(w/'native').glob('soma_variant_*.ml')};b={p.name:p.read_bytes()for p in(w/'other').glob('soma_variant_*.ml')};assert a==b
PY
cp "$WORK/hash" "$WORK/before.hash"
python3 - "$WORK/app/protocol.definition" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);p.write_text(p.read_text().replace('"Timeout"','"Expired"'))
PY
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/after.hash"
if cmp -s "$WORK/before.hash" "$WORK/after.hash";then echo 'generic schema change did not change hashes' >&2;exit 1;fi
negative(){
 local name=$1 declaration=$2 source=$3 pattern=$4
 mkdir "$WORK/$name"
 cp "$HERE"/examples/example_projects/native_parametric_variants/* "$WORK/$name/"
 printf 'From Soma Require Native.\nImport protocol.\n%s\n' "$declaration" > "$WORK/$name/bad.definition"
 printf 'From Soma Require Native.\nImport protocol bad.\n%s\n' "$source" > "$WORK/$name/main.soma"
 if "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/native" > "$WORK/$name.log" 2>&1;then echo "accepted $name" >&2;exit 1;fi
 grep -q "$pattern" "$WORK/$name.log"
}
negative duplicate 'OCaml Native Polymorphic Variant bad (A:Type;A:Type) := ["Value":A].' 'Definition main:=@bad.bad.' 'parameters must be distinct'
negative proof_parameter 'OCaml Native Polymorphic Variant bad (A:Prop) := ["Value":A].' 'Definition main:=@bad.bad.' 'sort Type or Set'
negative strict_proof_parameter 'OCaml Native Polymorphic Variant bad (A:SProp) := ["Value":A].' 'Definition main:=@bad.bad.' 'sort Type or Set'
negative value_parameter 'OCaml Native Polymorphic Variant bad (A:nat) := ["Empty"].' 'Definition main:=@bad.bad.' 'sort Type or Set'
negative higher_rank 'OCaml Native Polymorphic Variant bad (A:Type) := ["Value":forall(B:Type),B->B].' 'Definition main:=@bad.bad.' 'must be monomorphic'
negative wrong_view 'OCaml Native View bad : forall(A B:Type), event A -> Native.result B (Native.result unit (Native.result unit unit)).' 'Definition main:=@bad.bad.' 'View result must be'
negative wrong_build 'OCaml Native Construct bad : forall(A B:Type), B -> event A := "Value".' 'Definition main:=@bad.bad.' 'argument differs'
negative type_confusion '' 'Definition main (value:event string):event bool:=value.' 'cannot be applied\|expected\|has type'
negative parameter_order '' 'Definition main (value:channel string bool):channel bool string:=value.' 'cannot be applied\|expected\|has type'
negative handle_inspection '' 'Definition main {A:Type}(value:event A):nat:=match value with Native.Native_family id=>id end.' 'cannot be inspected'
# A monomorphic native implementation cannot satisfy a universal descriptor.
mkdir "$WORK/monomorphic"
cp "$HERE"/examples/example_projects/native_parametric_variants/* "$WORK/monomorphic/"
printf 'From Soma Require Native.\nImport protocol.\nOCaml Native External Callback bad : forall(A:Type), event A -> event A := "Protocol.echo_bool".\n' > "$WORK/monomorphic/bad.definition"
printf 'From Soma Require Native.\nImport protocol bad.\nDefinition main:=@bad.bad.\n' > "$WORK/monomorphic/main.soma"
"$SOMA" extract "$WORK/monomorphic/main.soma" -o "$WORK/monomorphic/native" > "$WORK/monomorphic.log" 2>&1
if ocaml dune build --root "$WORK/monomorphic/native" --profile release -j2 >> "$WORK/monomorphic.log" 2>&1;then echo 'accepted a monomorphic native implementation for forall descriptor' >&2;exit 1;fi
grep -q 'less general\|not as general\|polymorphic' "$WORK/monomorphic.log"
echo 'PASS: parameter/namespace ABI provenance, source hashes, logical parameter separation, typed view/build rejection and opaque family inspection guard'
if [ "${SOMA_TEST_HVF:-0}" = 1 ];then
 mkdir "$WORK/image"
 cp "$HERE"/examples/example_projects/native_parametric_variants/{protocol.definition,protocol.ml} "$WORK/image/"
 printf '[project]\nname="native_parametric_image"\nversion="0.1.0"\n' > "$WORK/image/soma.toml"
 printf 'From Soma Require Native.\ninvoke : (unit -> Native.entry string) -> string.\n' > "$WORK/image/caller.definition"
 printf 'let invoke body=body()\n' > "$WORK/image/caller.ml"
 cat > "$WORK/image/main.soma" <<'SOMA'
Require Import Sandbox.
From Soma Require Native.
Import protocol caller.
Definition probe:=Native.Export(Native.Bind(Native.Call_callback make tt)(fun value=>
 Native.Bind(Native.Call_callback(@inspect string)value)(fun result=>
 Native.Return(match result with Native.Ok text=>text|Native.Error _=>"missing"end)))).
Definition main:io unit:=text<-call(fun _=>invoke(fun _=>probe));;
 if String.eqb text "generic native variant"then print "generic native variants in Solo5 verified"else exit 1.
SOMA
 SOMA_MIRAGE_SWITCH=${SOMA_MIRAGE_SWITCH:-kykeon} SOMA_MIRAGE_DIR="$WORK/image-project" SOMA_OCAML_BINDINGS_MODULE=Generic_image_bindings \
  "$SOMA" build "$WORK/image/main.soma" > "$WORK/image-build.log" 2>&1
 timeout 30 opam exec --switch="${SOMA_MIRAGE_SWITCH:-kykeon}" -- solo5-hvt --mem=256 -- "$WORK/image/main.hvt" > "$WORK/image-boot.log" 2>&1
 grep -q 'generic native variants in Solo5 verified' "$WORK/image-boot.log"
 echo 'PASS: parameterized native variant executes inside actual Solo5'
fi
echo 'parametric native variants: ok'
