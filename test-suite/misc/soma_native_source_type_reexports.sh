#!/usr/bin/env bash
# Cross-module nominal type equations are derived from checked Source shapes.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 30 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >schema.soma <<'SOMA'
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String.
Inductive json(F:Type) := Null | Bool(value:bool) | Num(value:F) | Str(value:string)
 | Arr(values:list(json F)) | Obj(fields:list(string*json F)).
Record inbox := Inbox {host:string;port:PrimInt63.int;token:string}.
Record box(A:Type) := Box {payload:A;index:PrimInt63.int}.
Inductive indexed(n:nat) := Index(value:bool).
Record higher := Higher {run:forall A:Type,A->A}.
Record empty_record := Empty_record {}.
Definition main := true.
SOMA
cat >exports.definition <<'SOMA'
From Soma Require Import Native.
From Stdlib Require Import Strings.String.
Import schema.
OCaml Native External Type real := "Float.t".
OCaml Native External Type native_json(F:Type) := "Target.json".
Fail OCaml Native Reexport Source bad := schema.main As "bad" From "Target.json".
Fail OCaml Native Reexport Source bad := schema.json As "bad;code" From "Target.json".
Fail OCaml Native Reexport Source bad := schema.json As "bad.name" From "Target.json".
Fail OCaml Native Reexport Source bad := schema.json As "bad" From "Target.json;code".
Fail OCaml Native Reexport Source bad := schema.indexed As "bad" From "Target.indexed".
Fail OCaml Native Reexport Source bad := schema.higher As "bad" From "Target.higher".
Fail OCaml Native Reexport Source bad := schema.empty_record As "bad" From "Target.empty_record".
Fail OCaml Native Reexport Source bad := True As "bad" From "Target.truth".
Fail OCaml Native Reexport Type bad As "bad" := (forall A:Type,A -> A).
OCaml Native Reexport Source public_json_value := schema.json As "json_value" From "Target.json".
Fail OCaml Native Reexport Source duplicate := schema.json As "json_value" From "Target.json".
OCaml Native Reexport Source public_inbox := schema.inbox As "inbox" From "Target.inbox".
OCaml Native Reexport Source public_box := schema.box As "box_value" From "Target.box".
OCaml Native Reexport Type public_json As "json" := (native_json real).
OCaml Native Reexport Type public_fn As "fn" := (bool -> bool).
SOMA
cat >main.soma <<'SOMA'
Import exports.
Definition main := (public_json_value,(public_inbox,(public_box,(public_json,public_fn)))).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import shlex,hashlib
rows=Path('native/native_source_type_reexports.manifest').read_text().splitlines()
assert rows[0]=='soma-native-source-type-reexports-v1' and len(rows)==6
files=set();names=[]
for line in rows[1:]:
 symbol,namespace,source,src_hash,name,digest,public,target,order=shlex.split(line)
 assert namespace=='exports' and symbol.startswith('exports.')
 assert hashlib.sha256(Path(source).read_bytes()).hexdigest()==src_hash
 assert hashlib.sha256(Path('native',name).read_bytes()).hexdigest()==digest
 assert int(order)==len(names);names.append(public);files.add(name)
assert names==['json_value','inbox','box_value','json','fn'] and len(files)==1
Path('types.ml').write_bytes(Path('native',files.pop()).read_bytes())
Path('types.mli').write_bytes(Path('types.ml').read_bytes())
for line in Path('hash.log').read_text().splitlines():
 assumptions=set(line.split('  assumes ',1)[1].split(', '))if'  assumes 'in line else set()
 assert assumptions<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},assumptions
PY
cp native/uint63.ml .
cat >target.ml <<'ML'
type 'a json=Null|Bool of bool|Num of 'a|Str of string|Arr of 'a json list|Obj of(string*'a json)list
type inbox={host:string;port:int;token:string}
type 'a box={payload:'a;index:int}
ML
cat >check.ml <<'ML'
module T=Types
let require name condition=if not condition then failwith name
let as_public(value:'a Target.json):'a T.json_value=value
let as_native(value:'a T.json_value):'a Target.json=value
let ()=
 let integers=Target.Arr[Target.Num 3;Target.Obj["x",Target.Bool true]]in
 let strings=Target.Obj["x",Target.Str "text"]in
 require "generic recursive nominal identity" (as_public integers==integers && as_native(as_public strings)==strings);
 (match as_public integers with T.Arr[T.Num 3;T.Obj["x",T.Bool true]]->()|_->assert false);
 let number:T.json=T.Num 1.25 in require "closed native type alias" (match number with Target.Num 1.25->true|_->false);
 let record:Target.inbox={host="localhost";port=80;token="token"}in
 let public:T.inbox=record in require "record labels and nominal identity" (public==record && public.T.host="localhost");
 let ints:int T.box_value={T.payload=7;index=3}and texts:string T.box_value={T.payload="x";index=4}in
 let native:int Target.box=ints in require "generic record equation" (native==ints && texts.T.payload="x");
 let callback:T.fn=fun x->x in let native:bool->bool=callback in require "function alias identity" (callback==native);
 Gc.full_major();let before=Gc.allocated_bytes()in
 for _=1 to 10000 do ignore(as_native(as_public integers))done;
 let cost=Gc.allocated_bytes()-.before in
 let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore integers done;
 require "type reexports allocate no conversion objects" (cost=Gc.allocated_bytes()-.before);
 print_endline "PASS: recursive constructors, generic records, original objects, closed aliases and no conversion allocation"
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -w -a uint63.ml target.ml types.mli types.ml check.ml -o check >"$compiler.log" 2>&1
 ./check
done
# Native typing checks the shape against the actual external owner as well.
cp target.ml target-good.ml
sed -i.bak 's/port:int/port:string/' target.ml
if ocamlc -w -a -c target.ml types.mli >wrong-owner.log 2>&1;then
 echo 'wrong native record shape was accepted';exit 1
fi
mv target-good.ml target.ml
cp hash.log before.log
sed -i.bak 's/As "json_value"/As "json_view"/' exports.definition
soma hash main.soma -no-soma-prelude >after.log
python3 - <<'PY'
from pathlib import Path
def main(file):return next(l.split()[0]for l in Path(file).read_text().splitlines()if l.split()[2]=='main.main')
assert main('before.log')!=main('after.log')
PY
cat >main.soma <<'SOMA'
Definition main := true.
SOMA
soma extract main.soma -no-soma-prelude -o native >plain.log 2>&1
test ! -e native/native_source_type_reexports.manifest
if find native -name 'soma_source_types_*.exports' | grep -q .;then echo 'stale Source type scope';exit 1;fi
printf 'PASS: Source/target type validation, provenance, semantic identities and cleanup\n'
