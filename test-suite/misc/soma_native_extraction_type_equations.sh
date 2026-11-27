#!/usr/bin/env bash
# Existing imported types are equated in place, preserving complete old units.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 25 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >origin.soma <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
Inductive kind:=Unknown|Flag(value:bool)|Count(value:nat)|Payload(value:buffer).
Record routes(A B:Type):={run:A->promise B;finish:B->unit}.
Record bad:={evidence:True;value:nat}.
Definition polymorphic:=forall A:Type,A->A.
Record poly_routes:={poly_field:polymorphic;other:nat}.
Record unused:={unused_field:nat;other_field:bool}.
Definition main:=(Unknown,@run).
SOMA
cat >client.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import origin.
Definition score value:=match value with Unknown=>0|Flag b=>if b then 1 else 2|Count n=>n|Payload _=>3 end.
Definition execute{A B:Type}(ops:routes A B)value:=@run A B ops value.
Definition body:=let _ := (bad,poly_routes) in (score,@execute).
Definition main:=body.
SOMA
soma extract origin.soma -no-soma-prelude -o origin-native >origin.log 2>&1
soma extract client.soma -no-soma-prelude -o baseline-native >baseline.log 2>&1
cp origin-native/prog.ml origin.ml
# This independent oracle is exactly the old Python header-rewrite algorithm,
# applied only in the fixture to a complete unannotated compiler unit.
python3 - <<'PY'
from pathlib import Path
import re
for suffix in ['.ml','.mli']:
 s=Path('baseline-native/prog'+suffix).read_text()
 s,n=re.subn(r'^type kind =', 'type kind = Origin.kind =',s,count=1,flags=re.M);assert n==1
 s,n=re.subn(r"^type \(([^)]+)\) routes =",lambda m:'type ('+m[1]+') routes = ('+m[1]+') Origin.routes =',s,count=1,flags=re.M);assert n==1
 Path('old'+suffix).write_text(s)
Path('old_build.ml').write_text('module Make()=struct\n'+Path('old.ml').read_text()+'\nend\n')
PY
cat >>client.soma <<'SOMA'
Fail OCaml Native Type Equation body Reuse origin.kind As "Origin.kind".
Fail OCaml Native Type Equation main Reuse score As "Origin.kind".
Fail OCaml Native Type Equation main Reuse origin.unused As "Origin.unused".
Fail OCaml Native Type Equation main Reuse origin.bad As "Origin.bad".
Fail OCaml Native Type Equation main Reuse origin.poly_routes As "Origin.poly_routes".
Fail OCaml Native Type Equation main Reuse origin.kind As "kind".
Fail OCaml Native Type Equation main Reuse origin.kind As "Origin.kind;let bad=1".
Fail OCaml Native Type Equation main Reuse origin.kind As "Client.kind".
OCaml Native Type Equation main Reuse origin.kind As "Origin.kind".
Fail OCaml Native Type Equation main Reuse origin.kind As "Origin.kind".
OCaml Native Type Equation main Reuse origin.routes As "Origin.routes".
SOMA
soma extract client.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash client.soma -no-soma-prelude >hash.log
cp native/prog.ml fresh.ml
cp native/prog.mli fresh.mli
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
rows=Path('native/native_type_equations.manifest').read_text().splitlines();assert rows[0]=='soma-native-type-equations-v1'
rows=[shlex.split(l)for l in rows[1:]];assert [r[3]for r in rows]==['origin.kind','origin.routes']
assert [r[6]for r in rows]==['0','2']
abis=[shlex.split(l)for l in Path('native/native_abi.manifest').read_text().splitlines()[1:]]
for owner,source,src,original,target,name,arity,prog,mli,identity in rows:
 assert hashlib.sha256(Path(source).read_bytes()).hexdigest()==src
 assert hashlib.sha256(Path('native/prog.ml').read_bytes()).hexdigest()==prog
 assert hashlib.sha256(Path('native/prog.mli').read_bytes()).hexdigest()==mli
 assert any(symbol==owner and h==src and hashlib.sha256(i.replace('\\n','\n').encode()).hexdigest()==identity for symbol,_,h,i in abis)
Path('fresh_build.ml').write_text('module Make()=struct\n'+Path('fresh.ml').read_text()+'\nend\n')
for line in Path('hash.log').read_text().splitlines():
 assumptions=set(line.split('  assumes ',1)[1].split(', '))if'  assumes 'in line else set()
 assert assumptions<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},assumptions
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cat >check.ml <<'ML'
module A(X:module type of Old)=struct end
module B(X:module type of Fresh)=struct end
module AB=A(Fresh)
module BA=B(Old)
let require label ok=if not ok then failwith label
let[@inline never] allocation f=Gc.full_major();let start=Gc.allocated_bytes()in
 for _=1 to 1000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.start
let ()=
 let bytes=Bytes.make 1048576 'x'in
 List.iter(fun value->require "all original constructor results"(Old.score value=Fresh.score value))
 [Origin.Unknown;Origin.Flag true;Origin.Flag false;Origin.Count 37;Origin.Payload bytes];
 let value:Fresh.kind=Fresh.Payload bytes in require "original payload"(match value with Origin.Payload raw->raw==bytes|_->false);
 let key=Lwt.new_key()in let seen=ref None in
 let pending,wake=Lwt.task()in let calls=ref 0 in let failure=Failure "type equation"in let broken=ref false in
 let ops:(string,bytes)Origin.routes={run=(fun _->incr calls;seen:=Lwt.get key;if !broken then raise failure;pending);finish=ignore}in
 require "complete generic record and original promise/context"(Lwt.with_value key(Some 19)(fun()->Fresh.execute ops "input")==pending&& !seen=Some 19);
 broken:=true;require "original fault"(try ignore(Fresh.execute ops "fault");false with e->e==failure);broken:=false;
 let old=allocation(fun()->Old.execute ops "input")and fresh=allocation(fun()->Fresh.execute ops "input")in require "exact call allocation"(old=fresh);
 let a=allocation(fun()->let module M=Old_build.Make()in M.score)and b=allocation(fun()->let module M=Fresh_build.Make()in M.score)in
 require "same complete unit and brand initialization allocation"(a=b);
 Lwt.wakeup wake bytes;require "original payload result"(Lwt_main.run pending==bytes);
 let p,_=Lwt.task()in let ops={ops with Origin.run=(fun _->p)}in let result=Fresh.execute ops "cancel"in Lwt.cancel result;
 require "original cancellation"(p==result&&Lwt.state p=Lwt.Fail Lwt.Canceled);
 let released=Weak.create 1 in let kept=ref None in
 let[@inline never] install()=let owner=Bytes.make 1048576 'o'in Weak.set released 0(Some owner);
 kept:=Some{Origin.run=(fun _->Lwt.return owner);finish=ignore}in
 install();Gc.full_major();Gc.full_major();require "live record owner"(Weak.check released 0);
 (match !kept with Some ops->ignore(Fresh.execute ops "owned")|_->assert false);
 kept:=None;Gc.full_major();Gc.full_major();require "natural record release"(not(Weak.check released 0));
 Printf.printf "PASS: complete constructor/record/generic APIs, original promise/context/fault/cancel/payload, exact call %.0f/%.0f B and unit initialization %.0f/%.0f B, natural Weak ownership.\n"old fresh a b
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt.unix -linkpkg -w -a uint63.ml soma_nat.ml soma_word64.ml soma_handles.ml soma_effect.ml float64.ml origin.ml old.mli old.ml fresh.mli fresh.ml old_build.ml fresh_build.ml check.ml -o check >"$compiler.log" 2>&1
 ./check
done
cat >proxy.soma <<'SOMA'
Import client.
Definition main:=(client.score,@client.execute).
SOMA
soma extract proxy.soma -no-soma-prelude -o proxy-native >proxy.log 2>&1
test ! -e proxy-native/native_type_equations.manifest
cp hash.log before-hash
cp native/native_abi.manifest before-abi
# A native target with a different name is legal syntax; native compilation is
# the representation check, and the metadata must distinguish that choice.
python3 - <<'PY'
from pathlib import Path
p=Path('client.soma');s=p.read_text();s=s.replace('Reuse origin.routes As "Origin.routes".','Reuse origin.routes As "Other.routes".');p.write_text(s)
PY
soma extract client.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash client.soma -no-soma-prelude >changed-hash.log
if cmp -s before-hash changed-hash.log||cmp -s before-abi changed/native_abi.manifest;then echo 'target missing from equation identity' >&2;exit 1;fi
cat >other.ml <<'ML'
type ('a,'b) routes={run:'a->'b;finish:'b->unit}
ML
ocamlfind ocamlc -package lwt.unix -c other.ml >other.log 2>&1
cp changed/prog.ml bad_target.ml
if ocamlfind ocamlc -package lwt.unix -c bad_target.ml >bad-target.log 2>&1;then
 echo 'incompatible actual target record accepted' >&2;exit 1
fi
if ! rg -q 'not included in|not compatible|not equal|do not match' bad-target.log;then cat bad-target.log >&2;exit 1;fi
printf 'Definition main:=true.\n' >client.soma
soma extract client.soma -no-soma-prelude -o native >cleanup.log 2>&1
test ! -e native/native_type_equations.manifest
printf 'PASS: checked targets/owners/shapes/dependencies, Source/product/ABI authentication, semantic sensitivity and stale metadata cleanup.\n'
