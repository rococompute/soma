#!/usr/bin/env bash
# Direct flat/nested tuple projections preserve whole programs and borrowed members.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 20 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type owner={bytes:bytes}
let count=ref 0
let weak=Weak.create 1
let fail=ref false
let fault=Failure "public projection"
let context:string Lwt.key=Lwt.new_key()
let response=ref(Lwt.return "ready")
let observe=ref(fun (_:owner) (_:string)->())
let prepare()=incr count;if !fail then raise fault;let owner={bytes=Bytes.make 65536 'x'}in
 let run text=(!observe)owner text;!response in let labelled ?prefix:_ text=run text in
 Weak.set weak 0(Some owner);owner,run,labelled
ML
cat >target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "Target.owner".
OCaml Native Callable labelled Optional prefix := forall(prefix:option string),string -> promise string.
OCaml Native External Callback prepare : unit -> Native.triple owner (string -> promise string) labelled := "Target.prepare".
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
From Corelib Require Import PrimInt63.
Import target.
Definition bindings:=Native.Export(Native.Call_callback prepare tt).
Definition unused:=bindings.
Definition nested:=(bindings,(true,Native.Triple 3%uint63 4%uint63 5%uint63)).
Definition keep{A:Type}(value:A):=value.
Definition main:=(nested,@keep).
SOMA
soma extract main.soma -no-soma-prelude -o baseline >baseline.log 2>&1
python3 - <<'PY'
from pathlib import Path
Path('before.ml').write_bytes(Path('baseline/prog.ml').read_bytes()+b'\nlet owner,run,labelled = bindings\nlet ((_,_,_),(flag,(_,last,_))) = nested\n')
Path('before.mli').write_bytes(Path('baseline/prog.mli').read_bytes()+b'\nval owner:Target.owner\nval run:string -> string Lwt.t\nval labelled:?prefix:string -> string -> string Lwt.t\nval flag:bool\nval last:Uint63.t\n')
PY
cat >>main.soma <<'SOMA'
Fail OCaml Native Public Projection bindings From bindings As "(owner,run,labelled)".
Fail OCaml Native Public Projection main From unused As "(owner,run,labelled)".
Fail OCaml Native Public Projection main From bindings As "(a,b)".
Fail OCaml Native Public Projection main From bindings As "(a,a,c)".
Fail OCaml Native Public Projection main From bindings As "(_,_,_)".
Fail OCaml Native Public Projection main From bindings As "whole".
Fail OCaml Native Public Projection main From bindings As "(a,b,c);let injected=()".
OCaml Native Public Projection main From bindings As "(owner,run,labelled)".
Fail OCaml Native Public Projection main From bindings As "(owner,other,third)".
OCaml Native Public Projection main From nested As "((_,_,_),(flag,(_,last,_)))".
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import shlex,hashlib
rows=Path('native/native_assemblies.manifest').read_text().splitlines();assert len(rows)==3
for row in rows[1:]:
 owner,source,src,file,h,ml,mli,bindings,layout,contract=shlex.split(row)
 for path,digest in [(source,src),('native/'+file,h),('native/prog.ml',ml),('native/prog.mli',mli),('native/soma_bindings.ml',bindings)]:assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest
 assert next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]==owner)==contract
for l in Path('hash.log').read_text().splitlines():assert'  assumes 'not in l or l.split('  assumes ',1)[1]=='Corelib.Numbers.Cyclic.Int63.PrimInt63.int'
Path('after.ml').write_bytes(Path('native/main.assembly').read_bytes());Path('after.mli').write_bytes(Path('native/main.assembly-interface').read_bytes())
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
 assert(!Target.count=2&&Before.flag&&After.flag&&Before.last=4&&After.last=4);
 let a,b,c=Before.bindings and x,y,z=After.bindings in
 assert(Before.owner==a&&Before.run==b&&Before.labelled==c&&After.owner==x&&After.run==y&&After.labelled==z);
 let check owner run (labelled:?prefix:string -> string -> string Lwt.t)=
  let pending,_=Lwt.task()in Target.response:=pending;
  Target.observe:=(fun actual text->assert(actual==owner&&text="hello"&&Lwt.get Target.context=Some "caller"));
  assert(Lwt.with_value Target.context(Some "caller")(fun()->run "hello")==pending);
  assert(Lwt.with_value Target.context(Some "caller")(fun()->labelled ~prefix:"kept" "hello")==pending);
  Target.observe:=(fun _ _->raise Target.fault);(try ignore(run "fault");assert false with ex->assert(ex==Target.fault));
  Target.observe:=(fun _ _->());assert(run "cancel"==pending);Lwt.cancel pending;assert(Lwt.state pending=Lwt.Fail Lwt.Canceled)
 in check Before.owner Before.run Before.labelled;check After.owner After.run After.labelled;
 let bytes=Bytes.make 8 'g'in assert(After.keep bytes==bytes&&After.keep true&&Before.keep "generic"="generic");
 Target.observe:=(fun _ _->());
 let before=allocated(fun()->let module M=Before_build.Make()in M.run)in
 let after=allocated(fun()->let module M=After_build.Make()in M.run)in assert(before=after);
 assert(allocated(fun()->Before.run "call")=allocated(fun()->After.run "call"));
 let lifetime make=
  let[@inline never] retain()=let run=make()in Gc.full_major();assert(Weak.check Target.weak 0);ignore(Sys.opaque_identity(run "keep"))in
  retain();Gc.full_major();Weak.check Target.weak 0 in
 let[@inline never] old()=let module M=Before_build.Make()in M.run in
 let[@inline never] fresh()=let module M=After_build.Make()in M.run in
 assert(not(lifetime old));assert(not(lifetime fresh));
 Target.fail:=true;(try let module M=After_build.Make()in ignore M.run;assert false with ex->assert(ex==Target.fault));
 Printf.printf "public projections: full flat/nested API, original tuple members/labels/promise/context/fault/cancel, exact init %.0f/call allocation and natural Weak passed\n%!"after
ML
for backend in ocamlopt ocamlc;do
 rm -f ./*.cm[iox] ./*.o
 ocamlfind "$backend" -w -a -package lwt.unix -linkpkg -I native soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml native/soma_callable_*.ml soma_bindings.ml before.mli before.ml after.mli after.ml before_build.ml after_build.ml check.ml -o check
 ./check
 done
cp main.soma original
# A public name must not hide an existing extracted helper, including one
# selected under another source-level spelling by extraction.
sed 's/(owner,run,labelled)/(keep,run,labelled)/g' original >main.soma
python3 - <<'PY'
from pathlib import Path
p=Path('main.soma');p.write_text('\n'.join(l for l in p.read_text().splitlines()if not l.startswith('Fail OCaml'))+'\n')
PY
if soma extract main.soma -no-soma-prelude -o collision >collision.log 2>&1;then echo 'accepted hidden helper' >&2;exit 1;fi
rg -q 'shadows an existing value' collision.log
cp original main.soma
sed 's/(owner,run,labelled)/(borrowed,run,labelled)/g' original >main.soma
python3 - <<'PY'
from pathlib import Path
p=Path('main.soma');p.write_text('\n'.join(l for l in p.read_text().splitlines()if not l.startswith('Fail OCaml'))+'\n')
PY
soma extract main.soma -no-soma-prelude -o renamed >renamed.log 2>&1
soma hash main.soma -no-soma-prelude >renamed-hash.log
python3 - <<'PY'
from pathlib import Path
old=next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]=='main.main')
new=next(l.split()[0]for l in Path('renamed-hash.log').read_text().splitlines()if l.split()[2]=='main.main')
assert old!=new
for suffix in ['.ml','.mli']:assert Path('native/prog'+suffix).read_bytes()==Path('renamed/prog'+suffix).read_bytes()
PY
# Ignored fields must also retain their native representation/arity.
python3 - <<'CHECK'
from pathlib import Path
import subprocess
cases=[('proof','Definition fields:=(I,true).','cannot erase proofs or types'),
 ('poly','Definition identity{A:Type}(x:A):=x. Definition fields:=(@identity,true).','must be monomorphic'),
 ('type','Definition fields:=(nat,true).','cannot erase proofs or types')]
for label,body,diagnostic in cases:
 Path('bad.soma').write_text('From Soma Require Import Native OCaml.\n'+body+'\nDefinition main:=fields.\nOCaml Native Public Projection main From fields As "(_, visible)".\n')
 result=subprocess.run(['soma','extract','bad.soma','-no-soma-prelude','-o','bad-'+label],capture_output=True,text=True)
 assert result.returncode and diagnostic in result.stdout+result.stderr,(label,result.stdout,result.stderr)
CHECK
cp original main.soma
cat >proxy.soma <<'SOMA'
Import main.
Definition main:=main.bindings.
SOMA
soma extract proxy.soma -no-soma-prelude -o proxy-native >proxy.log 2>&1
 test ! -f proxy-native/native_assemblies.manifest
sed '/OCaml Native Public Projection/d' original >main.soma
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
 test ! -f native/native_assemblies.manifest
 test ! -f native/main.assembly
 test ! -f native/main.assembly-interface
