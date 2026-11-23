#!/bin/sh
# Compiler-generated owned native types: offline host checks, optional Solo5.
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d "${TMPDIR:-/tmp}/soma-native-owned.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
ocaml() { if [ -n "${SOMA_NATIVE_TEST_SWITCH:-}" ]; then opam exec --switch="$SOMA_NATIVE_TEST_SWITCH" -- "$@"; else opam exec -- "$@"; fi; }
mkdir "$WORK/app"
cp "$HERE"/examples/example_projects/native_owned_records/* "$WORK/app/"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" >"$WORK/extract.log" 2>&1 || { cat "$WORK/extract.log";exit 1; }
(cd "$WORK/native" && ocaml dune build --profile release)
"$SOMA" hash "$WORK/app/main.soma" >"$WORK/hash"
python3 - "$WORK/native" "$WORK/app" "$WORK/hash" <<'PY'
import pathlib,sys,shlex,hashlib,re
out,app=map(pathlib.Path,sys.argv[1:3])
observed=set()
for line in pathlib.Path(sys.argv[3]).read_text().splitlines():
    if '  assumes ' in line:observed.update(line.split('  assumes ',1)[1].split())
assert observed=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},observed
assert not (out/'records.ml').exists()
assert (out/'native_owned.manifest').read_text().startswith('soma-native-owned-v1\n')
rows=[shlex.split(s)for s in(out/'native_owned.manifest').read_text().splitlines()[1:]]
modules={}
for symbol,source,source_hash,filename,generated_hash in rows:
    assert hashlib.sha256((app/source).read_bytes()).hexdigest()==source_hash
    assert hashlib.sha256((out/filename).read_bytes()).hexdigest()==generated_hash
    text=(out/filename).read_text()
    assert 'Obj.'not in text and 'Records.'not in text
    modules[symbol]=filename[:-3][0].upper()+filename[:-3][1:]
assert len(set(modules.values()))==len(rows)==4
assert modules['records.A.B.item']!=modules['records.A__B.item']
with(out/'probe.ml').open('w')as f:
    f.write('module Pipe='+modules['records.pipe']+'\nmodule Descriptor='+modules['records.descriptor']+'\n')
    f.write('module Left='+modules['records.A__B.item']+'\nmodule Right='+modules['records.A.B.item']+'\n')
    for name,symbol in re.findall(r'\(\* native records\.(\w+) \*\)\s*let (\w+) :',(out/'soma_bindings.ml').read_text()):
        f.write(f'let {name}=Soma_bindings.{symbol}\n')
assert 'native-owned-record'in(out/'native_abi.manifest').read_text()
print('PASS: source-only schemas, distinct namespaces, exact assumption audit and source/generated-type provenance')
PY
cat >>"$WORK/native/probe.ml" <<'ML'
let require name result=if not result then failwith name
(* A real consumer can re-export the exact generated representation. This
   alias preserves record identity and declaration order without a cycle. *)
type pipe=Pipe.t={mutable data:bytes;mutable offset:int;owner:Borrowed.node;callback:unit->unit Lwt.t}
let reexport(value:Pipe.t):pipe=value
module type Ops=sig
 type t
 val make:bytes->int->Borrowed.node->(unit->unit Lwt.t)->t
 val data:t->bytes
 val offset:t->int
 val owner:t->Borrowed.node
 val callback:t->unit->unit Lwt.t
 val set:t->int->unit
 val copy:t->int->t
end
module Raw=struct
 type t={mutable data:bytes;mutable offset:int;owner:Borrowed.node;callback:unit->unit Lwt.t}
 let make data offset owner callback={data;offset;owner;callback}
 let data x=x.data let offset x=x.offset let owner x=x.owner let callback x=x.callback
 let set x v=x.offset<-v let copy x offset={x with offset}
end
module Generated=struct
 type t=Pipe.t
 let make data offset owner callback=make_pipe(data,(offset,(owner,callback)))
 let data=get_data let offset=get_offset let owner=get_owner let callback=get_callback
 let set x v=set_offset(x,v)let copy x v=copy_offset(x,v)
end
let observations(module O:Ops)=
 let data=Bytes.of_string"ab"and owner=Borrowed.node"node"in
 let key=Lwt.new_key()in
 let promise,_=Lwt.task()in let callback()=require"dynamic callback context"(Lwt.get key=Some 31);promise in
 let original=O.make data 0 owner callback in
 let copied=O.copy original 7 in
 let aliases=O.data original==data&&O.owner original==owner&&O.callback original==callback&&
  copied!=original&&O.data copied==data&&O.owner copied==owner&&O.callback copied==callback in
 List.iter(fun n->O.set original n;require"signed native field"(O.offset original=n))[min_int;-1;0;1;max_int];
 Bytes.set data 0 'z';owner.Borrowed.label<-"changed";
 let alias_state=Bytes.to_string(O.data copied),(O.owner copied).Borrowed.label,O.offset copied in
 let seen=Lwt.with_value key(Some 31)(fun()->let f=O.callback original in require"callback scope"(Lwt.get key=Some 31);f())in
 require"promise identity"(seen==promise);Lwt.cancel promise;
 require"promise cancellation"(match Lwt.state seen with Lwt.Fail Lwt.Canceled->true|_->false);
 let reason=Failure"owned callback"in
 let failing=O.make data 0 owner(fun()->raise reason)in
 require"exception identity"(try ignore((O.callback failing)());false with e->e==reason);
 aliases,alias_state
let weak_checks(module O:Ops)=
 let create observe=
  let owner=Borrowed.node"weak"in let weak=Weak.create 1 in Weak.set weak 0(Some owner);
  let callback()=Gc.full_major();observe(Weak.check weak 0);Lwt.return_unit in
  O.make(Bytes.of_string"data")0 owner callback,weak in
 let invoke observe=let record,_=create observe in (O.callback record)()in
 let observed=ref None in ignore(invoke(fun seen->observed:=Some seen));
 let copied()=let record,_=create ignore in let weak=Weak.create 1 in Weak.set weak 0(Some record);O.copy record 9,weak in
 let clone,weak=copied()in Gc.full_major();
 let retained=Weak.check weak 0 in ignore(Sys.opaque_identity clone);
 !observed,retained
let ()=
 require"independent raw records"(observations(module Raw)=observations(module Generated));
 let raw=weak_checks(module Raw)and generated=weak_checks(module Generated)in
 require"weak lifetime equivalence"(raw=generated);
 Printf.printf"weak callback/copy-owner: raw=%s,%b generated=%s,%b\n"
  (match fst raw with None->"none"|Some x->string_of_bool x)(snd raw)
  (match fst generated with None->"none"|Some x->string_of_bool x)(snd generated);
 let node=Borrowed.node"nested"and bytes=Bytes.of_string"shared"in
 let callback()=Lwt.return_unit in
 let pipe=make_pipe(bytes,(1,(node,callback)))in
 require"reexport identity"(reexport pipe==pipe);
 require"external imported alias"(Prog.pass pipe==pipe);
 let fd=make_descriptor(pipe,(3,node))in require"nested owner identity"(get_pipe fd==pipe);
 set_offset(get_pipe fd,7);require"nested mutation"(get_offset pipe=7);
 let other=copy_offset(pipe,11)in set_pipe(fd,other);require"nested setter"(get_pipe fd==other&&get_offset pipe=7);
 require"Source entry ordinary ABI"(Prog.run node bytes callback=42);
 print_endline"PASS: native owned records preserve aliases, signed fields, copying, nested handles, callbacks/promises and Weak lifetimes"
ML
python3 - "$WORK/native" <<'PY'
import pathlib,sys
out=pathlib.Path(sys.argv[1]);modules=sorted(f.stem for f in out.glob('*.ml')if f.stem!='soma_main')
(out/'dune').write_text('(executable (name probe) (modes byte exe) (modules '+' '.join(modules)+') (libraries lwt) (flags (:standard -w -a)))\n')
PY
(cd "$WORK/native"&&ocaml dune build --profile release probe.exe probe.bc)
"$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"
# The carrier's only descriptor has no borrowed type in its result. Its opaque
# alias's phantom field-type dependencies must still pull Borrowed into output.
"$SOMA" extract "$WORK/app/carrier_main.soma" -o "$WORK/carrier" >"$WORK/carrier.log" 2>&1 || { cat "$WORK/carrier.log";exit 1; }
test -f "$WORK/carrier/borrowed.ml"
test ! -f "$WORK/carrier/carrier.ml"
(cd "$WORK/carrier"&&ocaml dune build --profile release)
printf '%s\n' 'PASS: owned field dependencies select borrowed modules without caller/schema-module cycles'
# Mutability/order metadata must invalidate the actual program contract and
# emitted module, even though the symbolic handle name stays fixed.
sed 's/mutable offset : int/offset : int/' "$WORK/app/records.definition" >"$WORK/changed"
mv "$WORK/changed" "$WORK/app/records.definition"
"$SOMA" hash "$WORK/app/main.soma" >"$WORK/changed-hash"
python3 - "$WORK/hash" "$WORK/changed-hash" <<'PY'
import pathlib,sys
main=lambda p:next(s.split()[0]for s in pathlib.Path(p).read_text().splitlines()if s.split()[2]=='main.main')
assert main(sys.argv[1])!=main(sys.argv[2])
print('PASS: owned schema metadata invalidates main.main contract')
PY
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/changed-native" >"$WORK/changed-extract.log" 2>&1 || { cat "$WORK/changed-extract.log";exit 1; }
python3 - "$WORK/native" "$WORK/changed-native" <<'PY_PROVENANCE'
import pathlib,shlex,sys
before,after=map(pathlib.Path,sys.argv[1:])
rows=lambda p:{r[0]:r for r in[shlex.split(s)for s in(p/'native_owned.manifest').read_text().splitlines()[1:]]}
a,b=rows(before)['records.pipe'],rows(after)['records.pipe']
assert a[2]!=b[2]and a[4]!=b[4]and a[3]==b[3]
assert (before/a[3]).read_bytes()!=(after/b[3]).read_bytes()
print('PASS: schema source and generated module digests change while canonical module name stays fixed')
PY_PROVENANCE
# A native module cannot shadow one of the standalone schema modules, including
# the case where it is an external library declaration without a companion ML.
module_name=$(python3 - "$WORK/native/native_owned.manifest" <<'PY_MODULE'
import shlex,sys
print(next(r[3][:-3]for r in map(shlex.split,open(sys.argv[1]).read().splitlines()[1:])if r[0]=='records.pipe'))
PY_MODULE
)
for mode in caller library;do
 mkdir "$WORK/collision-$mode"
 cp "$HERE"/examples/example_projects/native_owned_records/records.definition "$HERE"/examples/example_projects/native_owned_records/borrowed.* "$WORK/collision-$mode/"
 printf '%s\n' 'From Soma Require Native.' 'OCaml Native Callback clash:unit->unit:="clash".' >"$WORK/collision-$mode/$module_name.definition"
 if [ "$mode" = caller ];then printf '%s\n' 'let clash()=()' >"$WORK/collision-$mode/$module_name.ml";fi
 printf 'Import records %s.\nDefinition main:=(records.make_pipe,%s.clash).\n' "$module_name" "$module_name" >"$WORK/collision-$mode/main.soma"
 if "$SOMA" extract "$WORK/collision-$mode/main.soma" -o "$WORK/collision-$mode/out" >"$WORK/collision-$mode/log" 2>&1;then echo "FAIL generated module shadowed";exit 1;fi
 rg -q 'collides with a caller, native or reserved module' "$WORK/collision-$mode/log"||{ cat "$WORK/collision-$mode/log";exit 1; }
 printf 'PASS: rejected generated module collision with %s\n' "$mode"
done
mkdir "$WORK/namespace-negative"
cp "$HERE"/examples/example_projects/native_owned_records/records.definition "$HERE"/examples/example_projects/native_owned_records/borrowed.* "$WORK/namespace-negative/"
printf '%s\n' 'Import records.' 'Definition bad(value:records.A__B.item):records.A.B.item:=value.' 'Definition main:=bad.' >"$WORK/namespace-negative/main.soma"
if "$SOMA" extract "$WORK/namespace-negative/main.soma" -o "$WORK/namespace-negative/out" >"$WORK/namespace-negative/log" 2>&1;then echo "FAIL distinct owned record namespaces unified";exit 1;fi
rg -q 'expected.*type|has type' "$WORK/namespace-negative/log"||{ cat "$WORK/namespace-negative/log";exit 1; }
printf '%s\n' 'PASS: distinct owned record namespaces cannot unify'
mkdir "$WORK/inspection-negative"
cp "$HERE"/examples/example_projects/native_owned_records/records.definition "$HERE"/examples/example_projects/native_owned_records/borrowed.* "$WORK/inspection-negative/"
printf '%s\n' 'Import records.' 'From Soma Require Native.' 'Definition inspect(value:records.pipe):nat:=match value with Native.Native_handle id=>id end.' 'Definition main:=inspect.' >"$WORK/inspection-negative/main.soma"
if "$SOMA" extract "$WORK/inspection-negative/main.soma" -o "$WORK/inspection-negative/out" >"$WORK/inspection-negative/log" 2>&1;then echo "FAIL owned native handle inspected";exit 1;fi
rg -q 'Native programs and entry points cannot be inspected' "$WORK/inspection-negative/log"||{ cat "$WORK/inspection-negative/log";exit 1; }
printf '%s\n' 'PASS: owned native handle inspection remains forbidden'
# Long valid Source names must not exceed the filesystem's basename bound.
python3 - "$WORK/long" <<'PY_LONG'
import pathlib,sys
p=pathlib.Path(sys.argv[1]);p.mkdir();namespace='n'*70;name='r'*60
(p/(namespace+'.definition')).write_text('From Soma Require Native.\nOCaml Native Record '+name+':={mutable value:int}.\nOCaml Native Build make_item:int->'+name+':="value".\n')
(p/'main.soma').write_text('Import '+namespace+'.\nDefinition main:='+namespace+'.make_item.\n')
PY_LONG
"$SOMA" extract "$WORK/long/main.soma" -o "$WORK/long/out" >"$WORK/long/log" 2>&1||{ cat "$WORK/long/log";exit 1; }
python3 - "$WORK/long/out" <<'PY_LONG_CHECK'
import pathlib,shlex,sys
p=pathlib.Path(sys.argv[1]);rows=[shlex.split(s)for s in(p/'native_owned.manifest').read_text().splitlines()[1:]]
assert len(rows)==1 and len(rows[0][3].encode())<=100
(p/'dune').write_text((p/'dune').read_text().replace('(modes exe)','(modes byte exe)'))
PY_LONG_CHECK
(cd "$WORK/long/out"&&ocaml dune build --profile release soma_main.exe soma_main.bc)
"$WORK/long/out/_build/default/soma_main.exe"
ocaml ocamlrun "$WORK/long/out/_build/default/soma_main.bc"
printf '%s\n' 'PASS: long valid Source namespace/record names compile in native and bytecode modes'
# Negative schemas are rejected before a fake native module is required.
negative(){
 name=$1;schema=$2;extra=$3;phase=$4;message=$5
 mkdir "$WORK/$name"
 printf '%s\n' 'From Soma Require Native.' "$schema" "$extra" >"$WORK/$name/schema.definition"
 printf '%s\n' 'Import schema.' 'Definition main:=schema.bad.' >"$WORK/$name/main.soma"
 if "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/out" >"$WORK/$name/log" 2>&1;then
  [ "$phase" = ocaml ]||{ echo "FAIL $name accepted";exit 1; }
  if(cd "$WORK/$name/out"&&ocaml dune build --profile release)>>"$WORK/$name/log" 2>&1;then echo "FAIL $name compiled";exit 1;fi
 else [ "$phase" = soma ]||{ cat "$WORK/$name/log";exit 1; };fi
 rg -q "$message" "$WORK/$name/log"||{ cat "$WORK/$name/log";exit 1; }
 printf 'PASS: rejected %s\n' "$name"
}
negative duplicate 'OCaml Native Record item:={x:int;x:int}.' 'OCaml Native Get bad:item->int:="x".' soma 'owned record fields must be distinct'
negative polymorphic 'OCaml Native Record item:={x:forall A,A->A}.' 'OCaml Native Get bad:item->int:="x".' soma 'polymorphic owned fields'
negative unknown_type 'OCaml Native Record item:={x:Any}.' 'OCaml Native Get bad:item->int:="x".' soma 'Any has no OCaml type'
negative immutable 'OCaml Native Record item:={x:int}.' 'OCaml Native Set bad:item->int->unit:="x".' ocaml 'not mutable'
negative missing 'OCaml Native Record item:={x:int}.' 'OCaml Native Get bad:item->int:="absent".' ocaml 'Unbound record field'
negative wrong_type 'OCaml Native Record item:={x:int}.' 'OCaml Native Get bad:item->bool:="x".' ocaml 'expected of type'
negative incomplete 'OCaml Native Record item:={x:int;y:int}.' 'OCaml Native Build bad:int->item:="x".' ocaml 'record fields are undefined'
negative recursive 'OCaml Native Record item:={next:item}.' 'OCaml Native Get bad:item->int:="next".' soma 'reference item was not found'
if [ "${SOMA_TEST_HVF:-0}" = 1 ];then
 mkdir "$WORK/image"
 cp "$HERE"/examples/example_projects/native_owned_records/*.definition "$HERE"/examples/example_projects/native_owned_records/*.ml "$WORK/image/"
 cp "$HERE/examples/example_projects/native_owned_records/main.soma" "$WORK/image/policy.soma"
 cp "$HERE/examples/example_projects/native_owned_records/main.exp" "$WORK/image/policy.exp"
 printf '[project]\nname="native_owned_image"\nversion="0.1.0"\n' >"$WORK/image/soma.toml"
 printf '%s\n' 'Require Import Soma.Native.' 'invoke:((unit->promise unit)->entry nat)->nat.' >"$WORK/image/caller.definition"
 printf '%s\n' 'let invoke body=body(fun()->Lwt.return_unit)' >"$WORK/image/caller.ml"
 cat >"$WORK/image/main.soma" <<'SOMA'
Require Import Sandbox.
From Soma Require Native.
Import policy records borrowed caller.
Definition native_probe callback:=Native.Export
 (Native.Bind(Native.Call_callback borrowed.make_node "image")(fun owner=>
 Native.Bind(Native.Call_callback borrowed.make_bytes "buffer")(fun data=>
 policy.run_program owner data callback))).
Definition main:io unit:=
 value <- call(fun _=>invoke(fun callback=>native_probe callback));;
 if Nat.eqb value 42 then print "owned native records in Solo5 verified" else exit 1.
SOMA
 image_dir=${SOMA_MIRAGE_DIR:-$WORK/image-project}
 if [ -n "${SOMA_NATIVE_IMAGE_TEMPLATE:-}" ];then
  template_dir="$image_dir/$(basename "$SOMA_NATIVE_IMAGE_TEMPLATE")"
  mkdir -p "$template_dir"
  rsync -a --exclude _build --exclude .git "$SOMA_NATIVE_IMAGE_TEMPLATE/" "$template_dir/"
 fi
 SOMA_MIRAGE_SWITCH=${SOMA_MIRAGE_SWITCH:-kykeon} SOMA_MIRAGE_DIR="$image_dir" \
  "$SOMA" build "$WORK/image/main.soma" >"$WORK/image-build.log" 2>&1||{ cat "$WORK/image-build.log";exit 1; }
 timeout 30 opam exec --switch="${SOMA_MIRAGE_SWITCH:-kykeon}" -- solo5-hvt --mem=256 -- "$WORK/image/main.hvt" >"$WORK/image-boot.log" 2>&1||{ cat "$WORK/image-boot.log";exit 1; }
 rg -q 'owned native records in Solo5 verified' "$WORK/image-boot.log"||{ cat "$WORK/image-boot.log";exit 1; }
 printf '%s\n' 'PASS: generated owned records compile and boot in actual Solo5 consumer'
fi
printf '%s\n' 'PASS: owned native record stage checks complete'
