#!/usr/bin/env bash
# Native type equations retain owned nominal identity and exact representation.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 40 "$work"/{extract,build}.log 2>/dev/null || true; fi; if [ "${KEEP:-0}" = 1 ]; then echo "Retained $work"; else rm -rf "$work"; fi; exit "$rc"' EXIT
cd "$work"
cat > schema.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Lists.List Strings.String.
OCaml Native Algebraic storage := [
 data := ["Disk" {off:PrimInt63.int;size:PrimInt63.int};"Mem" {mutable b:buffer;mutable size:PrimInt63.int}];
 kind := ["File" {mutable data:data};"Dir" Of [Native.table string node];"Name" Of [string]];
 node := {ino:PrimInt63.int;mutable kind:kind;mutable mode:PrimInt63.int}
] Exceptions ["Err" Of [PrimInt63.int]].
OCaml Native Algebraic image := [fimg := {span:PrimInt63.int*PrimInt63.int;mutable refs:PrimInt63.int}].
SOMA
cat > seed.soma <<'SOMA'
From Soma Require Import Native.
Import schema.
Definition main := Native.Export(Native.Return((@None node),(@None fimg))).
SOMA
soma extract seed.soma -no-soma-prelude -o seed-native >seed.log 2>&1
python3 - <<'PY'
from pathlib import Path
import shlex
entries={shlex.split(row)[0]:shlex.split(row)[3]for row in Path('seed-native/native_algebraic.manifest').read_text().splitlines()[1:]}
a=entries['schema.data'];b=entries['schema.fimg']
Path('target.ml').write_text('module Storage = '+Path(a).stem.capitalize()+'\nmodule Image = '+Path(b).stem.capitalize()+'\nmodule Wrong = struct\n'+Path('seed-native',a).read_text()+'end\nlet marker=()\n')
PY
cat > target.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native External Value marker:unit := "Target.marker".
SOMA
cat > aliases.definition <<'SOMA'
From Soma Require Import Native.
Import schema.
Module Storage.
OCaml Native Reexport Algebraic api := schema.data As "Target.Storage".
End Storage.
Module Image.
OCaml Native Reexport Algebraic api := schema.fimg As "Target.Image".
End Image.
Fail OCaml Native Reexport Algebraic not_owned := nat As "Target.Storage".
Fail OCaml Native Reexport Algebraic invalid_path := schema.data As "Target.lowercase".
Fail OCaml Native Reexport Algebraic invalid_code := schema.data As "Target.Storage; let bad = ()".
Module Duplicates.
OCaml Native Reexport Algebraic one := schema.node As "Target.Storage".
Fail OCaml Native Reexport Algebraic two := schema.kind As "Target.Storage".
End Duplicates.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import aliases target.
Definition main := (Storage.api,(Image.api,Native.Export(Native.Call_callback marker tt))).
SOMA
cat > main.exp <<'SOMA'
Theorem reexport_markers_are_canonical : Storage.api = tt /\ Image.api = tt.
Proof. split;reflexivity. Qed.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
lines=Path('native/native_algebraic_reexports.manifest').read_text().splitlines();assert lines[0]=='soma-native-algebraic-reexports-v1'
scopes={}
for row in lines[1:]:
 symbol,namespace,source,source_hash,filename,digest,owner,target,order=shlex.split(row)
 assert hashlib.sha256(Path(source).read_bytes()).hexdigest()==source_hash
 assert Path(filename).name==filename and filename.endswith('.exports')
 data=Path('native',filename).read_bytes();assert hashlib.sha256(data).hexdigest()==digest
 scopes[namespace]=filename
 # Only requested types: neither exceptions nor provider/helper values.
 assert b'exception Err'not in data and b'let 'not in data
assert sorted(scopes)==['aliases.Duplicates','aliases.Image','aliases.Storage']
Path('names.ml').write_text(''.join('module '+namespace.rsplit('.',1)[1]+' = Soma_bindings.'+Path(filename).stem.capitalize()+'\n'for namespace,filename in sorted(scopes.items())))
for namespace,filename in scopes.items():Path('raw_'+namespace.rsplit('.',1)[1].lower()+'.ml').write_bytes(Path('native',filename).read_bytes())
assert 'native-algebraic-reexport'in Path('native/native_abi.manifest').read_text()
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_bindings.mli,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_algebraic_*.ml .
cat > check.ml <<'ML'
module R=Names.Storage
module I=Names.Image
let require name value=if not value then failwith name
let storage(value:R.node):Target.Storage.node=value
let raw(value:Raw_storage.node):R.node=value
let image(value:I.fimg):Target.Image.fimg=value
let ()=
 let bytes=Bytes.make 4096 'b'in
 let data=R.Mem{b=bytes;size=4096}in let kind=R.File{data}in
 let node:R.node={ino=31;kind;mode=7}in
 require "owned nominal data/node identity"(storage node==node&&raw node==node);
 require "borrowed inline mutable data"(match Target.Storage.(storage node).kind with Target.Storage.File{data=Target.Storage.Mem{b;size}}->b==bytes&&size=4096|_->false);
 R.(node.mode<-19);require "mutable field shared"(Target.Storage.(storage node).mode=19);
 (match kind with R.File fields->fields.data<-R.Disk{off=5;size=9}|_->assert false);
 require "constructor reexports preserve matching"(match Target.Storage.(storage node).kind with Target.Storage.File{data=Target.Storage.Disk{off=5;size=9}}->true|_->false);
 let children=Hashtbl.create 3 in Hashtbl.add children "self" node;
 node.kind<-R.Dir children;
 require "recursive borrowed table/child"(match Target.Storage.(storage node).kind with Target.Storage.Dir table->table==children&&Hashtbl.find table "self"==node|_->false);
 let f:I.fimg={span=(1,2);refs=1}in(image f).Target.Image.refs<-7;require "single-record alias and mutable identity"(I.(f.refs)=7);
 let old()=Target.Storage.{ino=31;kind=Name "node";mode=7}and current()=R.{ino=31;kind=Name "node";mode=7}in
 let measure fn=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.start in
 let a=measure old and b=measure current in require "exact constructor allocation"(a=b);
 Printf.printf "PASS: native algebraic reexports preserve owned/target nominal type identity, recursive constructors, inline records, mutable fields and borrowed buffers/tables/children, single records and exact allocation %.0f/%.0f B.\n%!"a b
ML
cat > bad_exception.ml <<'ML'
let unrelated=Names.Storage.Err 3
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml $(ocamldep -sort soma_algebraic_*.ml) target.ml soma_bindings.mli soma_bindings.ml prog.mli prog.ml names.ml raw_storage.ml raw_image.ml raw_duplicates.ml check.ml
 ./"check-$compiler"
 if ocamlfind "$compiler" -package lwt -c bad_exception.ml >bad-exception.log 2>&1;then echo 'unrelated exception leaked into reexport API' >&2;exit 1;fi
done
cp aliases.definition before-definition
cp native/native_abi.manifest before-abi
cp hash.log before-hash
sed -i.bak 's/As "Target.Storage"/As "Target.Wrong"/g' aliases.definition
soma extract main.soma -no-soma-prelude -o wrong >wrong.log 2>&1
soma hash main.soma -no-soma-prelude >wrong-hash
if cmp -s before-abi wrong/native_abi.manifest;then echo 'nominal target ABI unchanged' >&2;exit 1;fi
if cmp -s before-hash wrong-hash;then echo 'nominal target hash unchanged' >&2;exit 1;fi
if (cd wrong && dune build --profile release -j2)>wrong-build.log 2>&1;then echo 'same-shaped unrelated nominal target accepted' >&2;exit 1;fi
