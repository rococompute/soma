#!/usr/bin/env bash
# A record view changes a type declaration only, preserving all runtime objects.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 20 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >schema.soma <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
Record payload:={bytes:buffer;run:string -> promise string}.
Record wrong:={wrong_bytes:bool;wrong_run:string -> promise string}.
SOMA
cat >target.ml <<'ML'
type payload={bytes:bytes;run:string -> string Lwt.t}
let count=ref 0
let weak=Weak.create 1
let fail=ref false
let fault=Failure "record view"
let context:string Lwt.key=Lwt.new_key()
let response=ref(Lwt.return "ready")
let observe=ref(fun (_:bytes) (_:string)->())
let create()=incr count;if !fail then raise fault;let bytes=Bytes.make 65536 'x'in
 let run text=(!observe)bytes text;!response in let value={bytes;run}in Weak.set weak 0(Some value);value
ML
cat >target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native External Type item := "Target.payload".
OCaml Native External Type unused := "Target.payload".
OCaml Native External Callback create : unit -> item := "Target.create".
OCaml Native Get read_run : item -> (string -> promise string) := "run".
SOMA
cat >views.definition <<'SOMA'
From Soma Require Import Native Handles.
Import schema.
OCaml Native Reexport Source checked := schema.payload As "published" From "Target.payload".
OCaml Native Reexport Source other := schema.payload As "other" From "Other.payload".
OCaml Native Reexport Source wrong := schema.wrong As "wrong" From "Target.payload".
OCaml Native Reexport Type nonrecord As "nonrecord" := bool.
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import target views.
Definition assemble:=Native.Bind(Native.Call_callback create tt)(fun owner=>
 Native.Bind(Native.Call_callback read_run owner)(fun run=>Native.Return(owner,run))).
Definition bindings:=Native.Export assemble.
Definition keep{A:Type}(value:A):=value.
Definition main:=(bindings,@keep).
SOMA
soma extract main.soma -no-soma-prelude -o baseline >baseline.log 2>&1
# Independent former Python algorithm, applied only in this fixture to the
# complete original compiler program; no runtime declaration is omitted.
python3 - <<'PY'
from pathlib import Path
import re
for suffix in ['.ml','.mli']:
 s=Path('baseline/prog'+suffix).read_text()
 s,n=re.subn(r'^type item = Target.payload$', 'type item = Target.payload = {bytes:bytes;run:string -> string Lwt.t}',s,flags=re.M)
 assert n==1
 Path('before'+suffix).write_text(s)
PY
cat >>main.soma <<'SOMA'
Fail OCaml Native Record View bindings Replace target.item With views.checked.
Fail OCaml Native Record View main Replace target.unused With views.checked.
Fail OCaml Native Record View main Replace target.create With views.checked.
Fail OCaml Native Record View main Replace target.item With views.other.
Fail OCaml Native Record View main Replace target.item With views.nonrecord.
OCaml Native Record View main Replace target.item With views.checked.
Fail OCaml Native Record View main Replace target.item With views.checked.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
lines=Path('native/native_record_views.manifest').read_text().splitlines();assert lines[0]=='soma-native-record-views-v1'and len(lines)==2
owner,source,src,original,marker,target,name,ml,mli,identity=shlex.split(lines[1])
assert(owner,original,marker,target,name)==('main.main','target.item','views.checked','Target.payload','item')
for path,h in [(source,src),('native/prog.ml',ml),('native/prog.mli',mli)]:assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==h
abis=[shlex.split(l)for l in Path('native/native_abi.manifest').read_text().splitlines()[1:]]
assert any(o==owner and h==src and hashlib.sha256(i.replace('\\n','\n').encode()).hexdigest()==identity for o,_,h,i in abis)
for l in Path('hash.log').read_text().splitlines():assert'  assumes 'not in l or l.split('  assumes ',1)[1]=='Corelib.Numbers.Cyclic.Int63.PrimInt63.int'
for suffix in ['.ml','.mli']:Path('after'+suffix).write_bytes(Path('native/prog'+suffix).read_bytes())
for side in ['before','after']:Path(side+'_build.ml').write_text('module Make()=struct\n'+Path(side+'.ml').read_text()+'\nend\n')
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_bindings.ml} .
cat >check.ml <<'ML'
module A(X:module type of Before)=struct end
module B(X:module type of After)=struct end
module AB=A(After)
module BA=B(Before)
let[@inline never] allocated f=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 1000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.start
let ()=
 assert(!Target.count=2);
 let old,old_run=Before.bindings and fresh,fresh_run=After.bindings in
 let check owner run=
  assert(owner.Target.run==run);
  let pending,_=Lwt.task()in Target.response:=pending;
  Target.observe:=(fun bytes text->assert(bytes==owner.Target.bytes&&text="hello"&&Lwt.get Target.context=Some "caller"));
  assert(Lwt.with_value Target.context(Some "caller")(fun()->run "hello")==pending);
  Target.observe:=(fun _ _->raise Target.fault);
  (try ignore(run "fault");assert false with ex->assert(ex==Target.fault));
  Target.observe:=(fun _ _->());assert(run "cancel"==pending);Lwt.cancel pending;assert(Lwt.state pending=Lwt.Fail Lwt.Canceled)
 in check old old_run;check fresh fresh_run;
 let alias:After.item=old in assert(alias==old&&alias.bytes==old.bytes&&alias.run==old_run);
 let bytes=Bytes.make 8 'g'in assert(After.keep bytes==bytes&&After.keep true&&Before.keep "generic"="generic");
 Target.observe:=(fun _ _->());
 let before=allocated(fun()->let module M=Before_build.Make()in fst M.bindings)in
 let after=allocated(fun()->let module M=After_build.Make()in fst M.bindings)in assert(before=after);
 assert(allocated(fun()->old_run "call")=allocated(fun()->fresh_run "call"));
 let lifetime make=
  let[@inline never] retain()=let owner=make()in Gc.full_major();assert(Weak.check Target.weak 0);ignore(Sys.opaque_identity owner)in
  retain();Gc.full_major();Weak.check Target.weak 0 in
 let[@inline never] old()=let module M=Before_build.Make()in fst M.bindings in
 let[@inline never] fresh()=let module M=After_build.Make()in fst M.bindings in
 assert(not(lifetime old));assert(not(lifetime fresh));
 Target.fail:=true;(try let module M=After_build.Make()in ignore M.bindings;assert false with ex->assert(ex==Target.fault));
 Printf.printf "record views: full APIs/nominal fields, original objects/promise/context/fault/cancel, exact init %.0f, exact call allocation and natural Weak passed\n%!"after
ML
for backend in ocamlopt ocamlc;do
 rm -f ./*.cm[iox] ./*.o
 ocamlfind "$backend" -w -a -package lwt.unix -linkpkg -I native soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_bindings.ml before.mli before.ml after.mli after.ml before_build.ml after_build.ml check.ml -o check
 ./check
 done
# Even a publication-only name changes the checked owner identity while the
# actual allocated alias name and whole runtime program remain unchanged.
cp views.definition original-views
sed 's/As "published"/As "published_again"/' original-views >views.definition
soma extract main.soma -no-soma-prelude -o renamed >renamed.log 2>&1
soma hash main.soma -no-soma-prelude >renamed-hash.log
python3 - <<'CHECK'
from pathlib import Path
import shlex
old=next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]=='main.main')
new=next(l.split()[0]for l in Path('renamed-hash.log').read_text().splitlines()if l.split()[2]=='main.main')
assert old!=new
for suffix in ['.ml','.mli']:assert Path('native/prog'+suffix).read_bytes()==Path('renamed/prog'+suffix).read_bytes()
assert shlex.split(Path('native/native_record_views.manifest').read_text().splitlines()[1])[9]!=shlex.split(Path('renamed/native_record_views.manifest').read_text().splitlines()[1])[9]
CHECK
cp original-views views.definition
cp main.soma original
# Shape assertions are checked by the actual native compiler against the owner.
sed 's/With views.checked\./With views.wrong./g' original >main.soma
# Keep only the actual declaration: earlier Fail assertions belong to the
# positive Source and would mask the native ABI mismatch being exercised here.
python3 - <<'PY'
from pathlib import Path
p=Path('main.soma');p.write_text('\n'.join(l for l in p.read_text().splitlines()if not l.startswith('Fail OCaml'))+'\n')
PY
soma extract main.soma -no-soma-prelude -o wrong >wrong.log 2>&1
cp wrong/prog.mli wrong.mli
if ocamlfind ocamlc -package lwt.unix -I . -c wrong.mli >native-mismatch.log 2>&1;then echo 'accepted wrong native record shape' >&2;exit 1;fi
rg -qi 'does not match|do not match|field' native-mismatch.log
cp original main.soma
cat >proxy.soma <<'SOMA'
Import main.
Definition main:=main.bindings.
SOMA
soma extract proxy.soma -no-soma-prelude -o proxy-native >proxy.log 2>&1
 test ! -f proxy-native/native_record_views.manifest
# Obsolete metadata is cleaned after the declaration disappears.
sed '/OCaml Native Record View/d' original >main.soma
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
 test ! -f native/native_record_views.manifest
