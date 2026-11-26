#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 25 "$work"/*.log 2>/dev/null||true;fi;if [ "${KEEP:-0}" = 1 ];then echo "Retained $work";else rm -rf "$work";fi;exit "$rc"' EXIT
cd "$work"
cat >owner.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String.
OCaml Native Algebraic graph := [
 node := {mutable payload:option buffer;next:option node;edge:edge};
 edge := ["End";"Link" Of [node]];
 other := {text:string}
] Exceptions ["Empty";"Bad" Of [string];"Pair" Of [node;bool];"Details" {node:node;payload:buffer}].
OCaml Native External Type not_owned := "Bytes.t".
SOMA
cat >exports.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import List.
Import owner.
OCaml Native Reexport Record public_node := owner.node As "t".
OCaml Native Reexport Record public_other := owner.other As "standalone".
OCaml Native Reexport Exception public_bad := owner.node Constructor "Bad" As "Error".
OCaml Native Reexport Exception public_empty := owner.edge Constructor "Empty" As "Token".
OCaml Native Reexport Exception public_pair := owner.node Constructor "Pair" As "Pair".
OCaml Native Reexport Exception public_details := owner.other Constructor "Details" As "Details".
OCaml Native Reexport Type public_nodes As "nodes" := list owner.node.
Fail OCaml Native Reexport Record wrong_shape := owner.edge As "bad".
Fail OCaml Native Reexport Record wrong_owner := owner.not_owned As "bad".
Fail OCaml Native Reexport Record duplicate := owner.node As "t".
Fail OCaml Native Reexport Exception wrong_owner := owner.not_owned Constructor "Bad" As "Wrong".
Fail OCaml Native Reexport Exception missing := owner.node Constructor "Missing" As "Wrong".
Fail OCaml Native Reexport Exception lowercase := owner.node Constructor "Bad" As "wrong".
Fail OCaml Native Reexport Exception qualified := owner.node Constructor "Bad" As "Target.Wrong".
Fail OCaml Native Reexport Exception injected := owner.node Constructor "Bad" As "Wrong;code".
Fail OCaml Native Reexport Exception duplicate := owner.node Constructor "Empty" As "Token".
SOMA
cat >main.soma <<'SOMA'
Import exports.
Definition main := (public_node,public_other,public_bad,public_empty,public_pair,public_details,public_nodes).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import shlex,hashlib
rows=[shlex.split(row)for row in Path('native/native_source_type_reexports.manifest').read_text().splitlines()[1:]]
assert [row[6]for row in rows]==['t','standalone','Error','Token','Pair','Details','nodes']
assert [row[8]for row in rows]==list(map(str,range(7)))and len({row[4]for row in rows})==1
for symbol,namespace,source,digest,file,product,public,target,order in rows:
 assert namespace=='exports'and symbol.startswith(namespace+'.')
 assert hashlib.sha256(Path(source).read_bytes()).hexdigest()==digest
 assert hashlib.sha256(Path('native',file).read_bytes()).hexdigest()==product
assert all('  assumes 'not in line or line.split('  assumes ',1)[1]=='Corelib.Numbers.Cyclic.Int63.PrimInt63.int'for line in Path('hash.log').read_text().splitlines())
Path('raw.ml').write_bytes(Path('native',rows[0][4]).read_bytes())
owned=rows[0][7].rsplit('.',1)[0]
Path('names.ml').write_text('module Owner='+owned+'\n')
Path('before.ml').write_text(f'''type t = {owned}.node = {{mutable payload:bytes option;next:{owned}.node option;edge:{owned}.edge}}
type standalone = {owned}.other = {{text:string}}
exception Error = {owned}.Bad
exception Token = {owned}.Empty
exception Pair = {owned}.Pair
exception Details = {owned}.Details
type nodes = t list
''')
assert ('next : '+owned+'.node option')in Path('raw.ml').read_text()
assert ('edge : '+owned+'.edge')in Path('raw.ml').read_text()
PY
(cd native&&dune build --profile release -j2)>build.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cp native/soma_algebraic_*.ml .
cat >check.ml <<'ML'
module Owner=Names.Owner
module A(X:module type of Before)=struct end
module B(X:module type of Raw)=struct end
module AB=A(Raw)
module BA=B(Before)
let require label ok=if not ok then failwith label
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let rec node:Raw.t={payload=None;next=Some node;edge=Owner.Link node}in
 let nodes:Raw.nodes=[node]in require "recursive nominal owner"(match nodes with[n]->n==node|_->false);
 let original:Owner.node=node in require "record identity"(original==node);
 let message=Bytes.to_string(Bytes.make 4096 'e')in
 require "nullary exception identity"(Raw.Token==Owner.Empty&&Raw.Token==Before.Token);
 require "catch borrowed exception"(try raise(Raw.Error message)with Owner.Bad borrowed->borrowed==message);
 require "reverse alias catch"(try raise(Owner.Bad message)with Raw.Error borrowed->borrowed==message);
 require "multiargument identity"(match Raw.Pair(node,true)with Owner.Pair(borrowed,true)->borrowed==node|_->false);
 let bytes=Bytes.make 4096 'p'in
 require "inline exception identity"(match Raw.Details{node;payload=bytes}with Owner.Details{node=borrowed;payload}->borrowed==node&&payload==bytes|_->false);
 let measure f=collect();let start=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.start in
 let a=measure(fun()->Before.Error message)and b=measure(fun()->Raw.Error message)in require "exact exception allocation"(a=b);
 let c=measure(fun()->Before.Pair(node,true))and d=measure(fun()->Raw.Pair(node,true))in require "exact payload exception allocation"(c=d);
 let e=measure(fun()->({Before.payload=None;next=Some node;edge=Owner.Link node}:Before.t))and f=measure(fun()->({Raw.payload=None;next=Some node;edge=Owner.Link node}:Raw.t))in require "exact record allocation"(e=f);
 let weak=Weak.create 1 in
 let[@inline never] install()=let bytes=Bytes.make 1048576 'w'in Weak.set weak 0(Some bytes);node.payload<-Some bytes in
 install();collect();require "live mutable original owner"(Weak.check weak 0);original.payload<-None;collect();require "natural payload release"(not(Weak.check weak 0));
 Printf.printf "PASS: complete recursive/mutable record APIs and nominal identity, nullary/payload/inline exception slots, original payloads, allocation %.0f/%.0f %.0f/%.0f %.0f/%.0f B and natural Weak release.\n"a b c d e f
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml soma_algebraic_*.ml names.ml before.ml raw.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
python3 - <<'PY'
from pathlib import Path
p=Path('owner.definition');p.write_text(p.read_text().replace('"Bad" Of [string]','"Bad" Of [buffer]'))
PY
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
if cmp -s hash.log changed-hash.log||cmp -s before-abi changed/native_abi.manifest;then echo 'exception signature omitted from fingerprints' >&2;exit 1;fi
cat >main.soma <<'SOMA'
Definition main:=true.
SOMA
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
python3 - <<'PY'
from pathlib import Path
assert not Path('native/native_source_type_reexports.manifest').exists()
assert not list(Path('native').glob('soma_source_types_*.exports'))
PY
printf '%s\n' 'PASS: invalid ownership/shapes/names/collisions, authenticated Source/products, signature fingerprints, trusted assumptions and stale-product cleanup.'
