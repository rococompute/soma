#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?;if [ "$rc" != 0 ];then tail -n 60 "$WORK"/*.log 2>/dev/null||true;fi;rm -rf "$WORK"' EXIT
ocaml(){ opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }
mkdir "$WORK/app"
cp "$HERE"/examples/example_projects/native_immutable/* "$WORK/app/"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
python3 - "$WORK" <<'PY'
from pathlib import Path
import sys,shlex,hashlib
w=Path(sys.argv[1]);out=w/'native';rows=[shlex.split(s)for s in(out/'native_owned.manifest').read_text().splitlines()[1:]]
assert len(rows)==2
for symbol,source,digest,name,product in rows:
 assert hashlib.sha256((w/'app'/source).read_bytes()).hexdigest()==digest
 assert hashlib.sha256((out/name).read_bytes()).hexdigest()==product
 assert 'Obj.' not in(out/name).read_text()
assert 'native-immutable-record' in(out/'native_abi.manifest').read_text()
allowed={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int','Corelib.Floats.PrimFloat.float'};seen=set()
for line in(w/'hash').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen==allowed,seen
for symbol,_,_,name,_ in rows:
 if symbol.endswith('.file'):module=Path(name).stem;module=module[:1].upper()+module[1:];(out/'record-module').write_text(module)
PY
cat > "$WORK/native/probe.ml" <<'ML'
module R=RECORD_MODULE
let ensure label value=if not value then failwith label
let combine last missing=last&&missing
let raw length (file:R.t) index=combine(index=length file.R.lines-1)file.R.missing_nl
let observe implementation index mutation=
 let lines=[|"first";"second"|]and label=Bytes.to_string(Bytes.make 1001 'l')in
 let file=Prog.make label lines false 0.in let events=ref[]in
 let length actual=events:=(actual==lines,file.R.missing_nl)::!events;
  if mutation then Obj.set_field(Obj.repr file)2(Obj.repr true);Array.length actual in
 let result=implementation length file index in result,List.rev !events,file.R.missing_nl
let ()=
 let label=Bytes.to_string(Bytes.make 1024 'x')and lines=[|"first";"second"|]in
 let file=Prog.make label lines true 17.in
 ensure"record layout and borrowed native fields"(Obj.size(Obj.repr file)=4&&file.R.label==label&&file.R.lines==lines&&file.R.missing_nl&&file.R.time=17.);
 ensure"pure projections and native echo alias"(Prog.file_label file==label&&Prog.size file=2&&Prog.echo_file file==file);
 let l,(a,(m,t))=Prog.fields file in ensure"pattern projection aliases"(l==label&&a==lines&&m&&t=17.);
 List.iter(fun index->List.iter(fun mutation->ensure"native/bytecode immutable field load timing"(observe raw index mutation=observe Prog.key_fields index mutation))[false;true])[min_int;-1;0;1;2;max_int];
 let value=Prog.make_point 3.5in ensure"single-field float record"(Prog.point_value value=3.5&&Obj.tag(Obj.repr value)=Obj.double_array_tag);
 print_endline"PASS: immutable logical records: shared native ABI, constructors/projections/patterns, aliases, flat mixed/all-float layouts and backend field-load timing"
ML
python3 - "$WORK/native" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);f=p/'probe.ml';s=f.read_text().replace('RECORD_MODULE',(p/'record-module').read_text()).replace('0.in','0. in').replace('17.in','17. in').replace('3.5in','3.5 in');f.write_text(s)
mods=sorted(f.stem for f in p.glob('*.ml')if f.stem!='soma_main')
(p/'dune').write_text('(executable (name probe) (modes exe byte) (modules '+' '.join(mods)+') (libraries lwt) (flags (:standard -w -a)))\n')
PY
ocaml dune build --root "$WORK/native" --profile release probe.exe probe.bc > "$WORK/build.log" 2>&1
ocaml "$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"

# A constructor-only consumer must still select its standalone schema module.
cat > "$WORK/app/constructor_only.soma" <<'SOMA'
Import schema.
Definition main:=Build_point.
SOMA
"$SOMA" extract "$WORK/app/constructor_only.soma" -o "$WORK/constructor-only" > "$WORK/constructor-only.log" 2>&1
python3 - "$WORK" <<'PY'
from pathlib import Path
import sys
w=Path(sys.argv[1]);a={p.name:p.read_bytes()for p in(w/'native').glob('soma_owned_*.ml')};b={p.name:p.read_bytes()for p in(w/'constructor-only').glob('soma_owned_*.ml')}
assert a==b and len(a)==2,(a.keys(),b.keys())
PY
"$SOMA" hash "$WORK/app/constructor_only.soma" > "$WORK/before.hash"
python3 - "$WORK/app/schema.definition" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);p.write_text(p.read_text().replace('coordinate:','position:'))
PY
"$SOMA" hash "$WORK/app/constructor_only.soma" > "$WORK/after.hash"
if cmp -s "$WORK/before.hash" "$WORK/after.hash";then echo 'immutable schema field failed to change identity' >&2;exit 1;fi
negative(){
 local case_name=$1 declaration=$2 pattern=$3 ffi=${4:-0}
 mkdir "$WORK/$case_name"
 printf 'From Soma Require Native.\n%s\n' "$declaration" > "$WORK/$case_name/bad.definition"
 printf 'From Soma Require Native.\nImport bad.\nDefinition main:=bad.\n' > "$WORK/$case_name/main.soma"
 if [ "$ffi" = 1 ];then
  "$SOMA" extract "$WORK/$case_name/main.soma" -o "$WORK/$case_name/native" > "$WORK/$case_name.log" 2>&1
  if ocaml dune build --root "$WORK/$case_name/native" --profile release >> "$WORK/$case_name.log" 2>&1;then echo "accepted $case_name" >&2;exit 1;fi
 else
  if "$SOMA" extract "$WORK/$case_name/main.soma" -o "$WORK/$case_name/native" > "$WORK/$case_name.log" 2>&1;then echo "accepted $case_name" >&2;exit 1;fi
 fi
 grep -q "$pattern" "$WORK/$case_name.log"
}
negative mutable_field 'OCaml Native Immutable Record bad := { mutable value:string }.' 'cannot be mutable'
negative duplicate_field 'OCaml Native Immutable Record bad := { value:string; value:string }.' 'distinct'
negative polymorphic_field 'OCaml Native Immutable Record bad := { value:forall A:Type,A->A }.' 'polymorphic'
negative unrelated_definition 'OCaml Native Immutable Record cell := { value:string }. Definition bad:=17.' 'is a definition'
negative immutable_set 'OCaml Native Immutable Record cell := { value:string }. OCaml Native Set bad : cell -> string -> unit := "value".' 'Error:' 1
echo 'PASS: constructor-only discovery, stable cross-unit schemas, field identities and rejection of mutable/polymorphic/duplicate fields, unrelated definitions and native immutable writes'
if [ "${SOMA_TEST_HVF:-0}" = 1 ];then
 mkdir "$WORK/image"
 cp "$HERE/examples/example_projects/native_immutable/schema.definition" "$WORK/image/"
 printf '[project]\nname="native_immutable_image"\nversion="0.1.0"\n' > "$WORK/image/soma.toml"
 printf 'From Soma Require Native.\ninvoke : (unit -> Native.entry string) -> string.\n' > "$WORK/image/caller.definition"
 printf 'let invoke f = f ()\n' > "$WORK/image/caller.ml"
 cat > "$WORK/image/main.soma" <<'SOMA'
Require Import Sandbox.
From Soma Require Native.
From Corelib Require Import PrimFloat PrimInt63.
Import schema caller.
Definition probe:=Native.Export(Native.Bind(Native.Vector_of_list("native"::nil))(fun lines=>
 let value:=Build_file "immutable record" lines false 0%float in
 Native.Return(if PrimInt63.eqb(Native.vector_word_size(schema.lines value))1%uint63 then label value else "missing"))).
Definition main:io unit:=
 text<-call(fun _=>invoke(fun _=>probe));;
 if String.eqb text "immutable record"then print "immutable native records in Solo5 verified"else exit 1.
SOMA
 SOMA_MIRAGE_SWITCH=${SOMA_MIRAGE_SWITCH:-kykeon} SOMA_MIRAGE_DIR="$WORK/image-project" \
 SOMA_OCAML_BINDINGS_MODULE=Immutable_image_bindings "$SOMA" build "$WORK/image/main.soma" > "$WORK/image-build.log" 2>&1
 timeout 30 opam exec --switch="${SOMA_MIRAGE_SWITCH:-kykeon}" -- solo5-hvt --mem=256 -- "$WORK/image/main.hvt" > "$WORK/image-boot.log" 2>&1
 grep -q 'immutable native records in Solo5 verified' "$WORK/image-boot.log"
 echo 'PASS: shared immutable native record constructors/projections execute inside actual Solo5'
fi
echo 'native immutable records: ok'
