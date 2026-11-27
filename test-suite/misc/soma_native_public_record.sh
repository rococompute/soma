#!/usr/bin/env bash
# Flat field publications retain the original record, initialization and aliases.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 40 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
type owner={bytes:bytes}
let count=ref 0
let weak=Weak.create 1
let fault=Failure "public record"
let context:string Lwt.key=Lwt.new_key()
let fail=ref false
let response=ref(Lwt.return "ready")
let observe=ref(fun (_:owner) (_:string)->())
let create()=incr count;if !fail then raise fault;let v={bytes=Bytes.make 1048576 'x'}in Weak.set weak 0(Some v);v
let invoke owner text=(!observe)owner text;!response
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "Target.owner".
OCaml Native External Callback create : unit -> owner := "Target.create".
OCaml Native External Value invoke : owner -> string -> promise string := "Target.invoke".
OCaml Native Callable labelled Optional prefix := forall(prefix:option string),string -> promise string.
OCaml Native Wrap labels : Native.callback (option string) (Native.callback string (promise string)) -> labelled.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native OCaml.
From Stdlib Require Import Strings.String.
Import target.
Record public := {api_owner:target.owner;api_run:string -> promise string;api_labelled:labelled}.
Definition assemble := Native.Bind(Native.Call_callback create tt)(fun owner=>
 Native.Bind(Native.Call_callback invoke tt)(fun call=>
 Native.Bind(Native.New_callback2(fun _ prefix text=>Native.Return(call owner text)))(fun f=>
 Native.Bind(Native.Call_callback labels f)(fun labelled=>
 Native.Return {|api_owner:=owner;api_run:=call owner;api_labelled:=labelled|})))).
Definition bindings := Native.Export assemble.
Definition unused := bindings.
Definition identity{A:Type}(value:A) := value.
Definition main := (bindings,@identity).
Record other := {other_field:bool;other_second:bool}.
Fail OCaml Native Public Record bindings From bindings With [Field "run" := api_run].
Fail OCaml Native Public Record main From unused With [Field "run" := api_run].
Fail OCaml Native Public Record main From bindings With [Field "bad;code" := api_run].
Fail OCaml Native Public Record main From bindings With [Field "run" := api_run;Field "run" := api_owner].
Fail OCaml Native Public Record main From bindings With [Field "other" := other_field].
Fail OCaml Native Public Record main From bindings With [Field "run" := assemble].
OCaml Native Public Record main From bindings With
 [Field "owner" := api_owner;Field "run" := api_run;Field "labelled" := api_labelled].
Fail OCaml Native Public Record main From bindings With [Field "run" := api_run].
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
rows=Path('native/native_assemblies.manifest').read_text().splitlines();assert len(rows)==3
for row in rows[1:]:
 symbol,source,source_hash,file,digest,program,interface,bindings,layout,contract=shlex.split(row)
 for path,h in [(source,source_hash),('native/'+file,digest),('native/prog.ml',program),('native/prog.mli',interface),('native/soma_bindings.ml',bindings)]:assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==h
 assert next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]==symbol)==contract
for l in Path('hash.log').read_text().splitlines():
 assert '  assumes 'not in l or set(l.split('  assumes ',1)[1].split(', '))<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'}
ml=Path('native/prog.ml').read_text();mli=Path('native/prog.mli').read_text()
# Independent old emitter over the complete unmodified compiler program.
Path('before.ml').write_text(ml+'\nlet owner = bindings.api_owner\nlet run = bindings.api_run\nlet labelled = bindings.api_labelled\n')
Path('before.mli').write_text(mli+'\nval owner : Target.owner\nval run : string -> string Lwt.t\nval labelled : ?prefix:string -> string -> string Lwt.t\n')
Path('after.ml').write_bytes(Path('native/main.assembly').read_bytes())
Path('after.mli').write_bytes(Path('native/main.assembly-interface').read_bytes())
for name in ['owner','run','labelled']:assert 'let '+name+' = bindings.api_'+name in Path('after.ml').read_text()
assert 'module Checked'not in Path('after.ml').read_text()
for name in ['before','after']:
 Path(name+'_build.ml').write_text('module Make()=struct\n'+Path(name+'.ml').read_text()+'\nend\n')
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_bindings.ml} .
cat > check.ml <<'ML'
module A(X:module type of Before)=struct end
module B(X:module type of After)=struct end
module AB=A(After)
module BA=B(Before)
let ()=
 assert(!Target.count=2);
 assert(Before.owner==Before.bindings.api_owner&&After.owner==After.bindings.api_owner);
 assert(Before.run==Before.bindings.api_run&&After.run==After.bindings.api_run);
 assert(Before.labelled==Before.bindings.api_labelled&&After.labelled==After.bindings.api_labelled);
 let check owner run (labelled:?prefix:string -> string -> string Lwt.t)=
  let pending,wake=Lwt.wait()in Target.response:=pending;
  let seen=ref false in Target.observe:=(fun actual text->assert(actual==owner&&text="hello");assert(Lwt.get Target.context=Some "context");seen:=true);
  let output=Lwt.with_value Target.context(Some "context")(fun()->run "hello")in
  assert(!seen&&output==pending);
  let output=Lwt.with_value Target.context(Some "context")(fun()->labelled ~prefix:"ignored" "hello")in assert(output==pending);
  Lwt.wakeup wake "done";
  Target.observe:=(fun _ _->raise Target.fault);
  (try ignore(run "hello");assert false with ex->assert(ex==Target.fault));
  Target.observe:=(fun _ _->());
  let cancel,_=Lwt.task()in Target.response:=cancel;let output=run "cancel"in assert(output==cancel);Lwt.cancel output;
  assert(Lwt.state cancel=Lwt.Fail Lwt.Canceled)
 in check Before.owner Before.run Before.labelled;check After.owner After.run After.labelled;
 Target.observe:=(fun _ _->());
 let allocated f=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 1000 do f()done;Gc.allocated_bytes()-.start in
 let before=allocated(fun()->let module M=Before_build.Make()in ignore(Sys.opaque_identity M.owner))in
 let after=allocated(fun()->let module M=After_build.Make()in ignore(Sys.opaque_identity M.owner))in
 assert(before=after);
 let lifetime make=
  let[@inline never] retain()=let f=make()in Gc.full_major();assert(Weak.check Target.weak 0);ignore(Sys.opaque_identity(f "lifetime"))in
  retain();Gc.full_major();Weak.check Target.weak 0 in
 let[@inline never] old()=let module M=Before_build.Make()in M.run in
 let[@inline never] fresh()=let module M=After_build.Make()in M.run in
 assert(not(lifetime old));assert(not(lifetime fresh));
 Target.fail:=true;(try let module M=After_build.Make()in ignore M.owner;assert false with ex->assert(ex==Target.fault));
 Printf.printf "public record: complete API, identity, context/fault/cancel, allocation %.0f, lifetime passed\n%!"after
ML
for backend in ocamlopt ocamlc;do
 rm -f ./*.cm[iox] ./*.o
 ocamlfind "$backend" -w -a -package lwt.unix -linkpkg -I native soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml native/soma_callable_*.ml soma_bindings.ml before.mli before.ml after.mli after.ml before_build.ml after_build.ml check.ml -o check
 ./check
 done
# Publication identity changes with the requested public names, while the
# complete runtime program stays byte-identical. Imports must not publish an
# unrelated entrypoint's fields.
cp main.soma original
sed 's/Field "owner" := api_owner/Field "borrowed" := api_owner/' original >main.soma
soma extract main.soma -no-soma-prelude -o renamed >renamed.log 2>&1
soma hash main.soma -no-soma-prelude >renamed-hash.log
python3 - <<'CHECK'
from pathlib import Path
old=next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]=='main.main')
new=next(l.split()[0]for l in Path('renamed-hash.log').read_text().splitlines()if l.split()[2]=='main.main')
assert old!=new
for suffix in ['.ml','.mli']:assert Path('native/prog'+suffix).read_bytes()==Path('renamed/prog'+suffix).read_bytes()
CHECK
cp original main.soma
cat >proxy.soma <<'SOMA'
Import main.
Definition main:=main.bindings.
SOMA
soma extract proxy.soma -no-soma-prelude -o proxy-native >proxy.log 2>&1
 test ! -f proxy-native/native_assemblies.manifest
# Collision gates fail extraction rather than shadowing the original API.
sed 's/Field "owner" := api_owner/Field "bindings" := api_owner/' original >main.soma
if soma extract main.soma -no-soma-prelude -o bad >collision.log 2>&1;then echo 'accepted colliding field' >&2;exit 1;fi
rg -q 'shadows an existing extracted value' collision.log
cp original main.soma
# Invalid record representations must fail with their own diagnostic.
python3 - <<'CHECK'
from pathlib import Path
import subprocess
cases=[
 ('proof','Record r:={evidence:True;value:nat}. Definition bindings:={|evidence:=I;value:=0|}.','value','erased proof or type fields'),
 ('poly','Definition poly:=forall A:Type,A->A. Record r:={method:poly;value:nat}. Definition bindings:={|method:=fun A x=>x;value:=0|}.','value','must be monomorphic'),
 ('parameter','Record r(A:Type):={value:A;flag:bool}. Definition bindings:={|value:=0;flag:=true|}.','value','unparameterized'),
 ('singleton','Record r:={value:nat}. Definition bindings:={|value:=0|}.','value','unerased native record representation'),
]
for label,body,field,diagnostic in cases:
 Path('bad.soma').write_text('From Soma Require Import Native OCaml.\n'+body+'\nDefinition main:=bindings.\nOCaml Native Public Record main From bindings With [Field "published" := '+field+'].\n')
 result=subprocess.run(['soma','extract','bad.soma','-no-soma-prelude','-o','bad-'+label],capture_output=True,text=True)
 assert result.returncode and diagnostic in result.stdout+result.stderr,(label,result.stdout,result.stderr)
CHECK
# Cleanup after the Source no longer requests publications.
python3 - <<'PY'
from pathlib import Path
p=Path('main.soma');s=p.read_text();s=s[:s.index('Fail OCaml Native Public Record')];p.write_text(s)
PY
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
 test ! -f native/main.assembly
 test ! -f native/main.assembly-interface
 test ! -f native/native_assemblies.manifest
