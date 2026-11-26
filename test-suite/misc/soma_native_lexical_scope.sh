#!/usr/bin/env bash
# Lexical publication retains the old expression, abstract functor scope and callable types.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 35 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type owner={bytes:bytes;mutable calls:int}
let prepared=ref 0
let fail_prepare=ref false
let failure=Failure "lexical assembly"
let trace=ref []
let weak=Weak.create 1
let response=ref(Lwt.return "ready")
let context:string Lwt.key=Lwt.new_key()
let observe=ref(fun (_:owner) (_:string)->())
let create()=
 trace:="prepare":: !trace;incr prepared;if !fail_prepare then raise failure;
 let owner={bytes=Bytes.make 1048576 'o';calls=0}in Weak.set weak 0(Some owner);owner
let invoke ?(enabled=true) owner text=
 if not enabled then raise failure;owner.calls<-owner.calls+1;(!observe)owner text;!response
module type API=sig
 type owner
 val create:unit->owner
 val invoke:?enabled:bool->owner->string->string Lwt.t
end
ML
cat >target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "S.owner".
OCaml Native External Value create : unit -> owner := "S.create".
OCaml Native Callable invoke_call Optional enabled := forall (enabled:option bool),owner->string->promise string.
OCaml Native External Eta Function invoke : owner->string->promise string := "S.invoke" Using invoke_call.
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
From Stdlib Require Import List Strings.String.
Import target.
Definition identity(values:list string):=values.
Definition external(value:string):=value.
Definition body := Native.Export(
 Native.Bind(Native.Call_callback create tt)(fun create=>
 Native.Bind(Native.Call_callback invoke tt)(fun invoke=>
 Native.Invoke create(fun owner=>Native.Return(owner,(fun text=>invoke owner text)))))).
Definition main := ((@identity,@external),body).
Fail OCaml Native Lexical Scope main.
OCaml Native Static Assembly main As "Checked" With
 [Value "id" := identity;Value "first" := external;Value "second" := external;Value "bundle" := body].
Fail OCaml Native Lexical Scope identity.
Fail OCaml Native Lexical Scope main Open ["Target;bad"].
Fail OCaml Native Lexical Scope main Open ["Target";"Target"].
Fail OCaml Native Lexical Scope main Functor "bad" With ["S":"Target.API"].
Fail OCaml Native Lexical Scope main Functor "Make" With ["Checked":"Target.API"].
Fail OCaml Native Lexical Scope main Functor "Make" With ["S":"Target.API";"S":"Target.API"].
Fail OCaml Native Lexical Scope main Functor "Make" With ["S":"Target.API) = struct"].
OCaml Native Lexical Scope main Open ["Target"] Functor "Make" With ["S":"Target.API"].
Fail OCaml Native Lexical Scope main.
SOMA
cat >types.soma <<'SOMA'
From Soma Require Import Native OCaml.
From Stdlib Require Import List.
Definition items(A:Type):=list A.
Definition identity{A}(values:items A):=values.
Definition main:=@identity.
OCaml Native Static Assembly main As "Checked" With [Type "items" := items;Value "id" := identity].
Fail OCaml Native Lexical Scope main.
SOMA
soma hash types.soma -no-soma-prelude >types.log
cat >generic.soma <<'SOMA'
From Soma Require Import Native OCaml.
Definition identity{A:Type}(value:A):=value.
Definition main:=@identity.
OCaml Native Static Assembly main As "Checked" With [Value "id" := identity].
Fail OCaml Native Lexical Scope main.
SOMA
soma hash generic.soma -no-soma-prelude >generic.log
cat >nested_generic.soma <<'SOMA'
From Soma Require Import Native OCaml.
Definition identity{A:Type}(value:A):=value.
Definition bundle:=(@identity,true).
Definition main:=bundle.
OCaml Native Static Assembly main As "Checked" With [Value "bundle" := bundle].
Fail OCaml Native Lexical Scope main.
SOMA
soma hash nested_generic.soma -no-soma-prelude >nested-generic.log
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import shlex,hashlib
rows=Path('native/native_assemblies.manifest').read_text().splitlines()
r=shlex.split(rows[1]);symbol,source,src_hash,name,digest,program,interface,bindings,layout,contract=r
for path,expected in [(source,src_hash),('native/'+name,digest),('native/prog.ml',program),('native/prog.mli',interface),('native/soma_bindings.ml',bindings)]:
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==expected,path
assert next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]==symbol)==contract
abi=[shlex.split(l)for l in Path('native/native_abi.manifest').read_text().splitlines()[1:]]
identity=next(i for s,_,h,i in abi if s==symbol and h==src_hash).replace('\\n','\n')
assert 'native-lexical-scope-v1\ncapture-owned-callables' in identity
assert hashlib.sha256(identity.encode()).hexdigest()==layout
for line in Path('hash.log').read_text().splitlines():
 assumptions=set(line.split('  assumes ',1)[1].split(', '))if'  assumes 'in line else set()
 assert assumptions<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},assumptions
# Independent old driver recipe around the same freshly checked implementation.
out=['module Make (S:Target.API)=struct\nlet id,first,second,bundle=\n']
for filename in sorted({shlex.split(l)[3]for l in Path('native/native_callables.manifest').read_text().splitlines()[1:]}):
 data=Path('native',filename).read_text()
 assert data in Path('native/main.assembly').read_text()
 out+=['let module '+Path(filename).stem.capitalize()+'=struct\n',data,'end in\n']
out+=['let module Checked:sig\n',Path('native/prog.mli').read_text(),'end=struct\nmodule Soma_bindings=struct\n',Path('native/soma_bindings.ml').read_text(),'end\n',Path('native/prog.ml').read_text(),'end in\nChecked.identity,Checked.external0,Checked.external0,Checked.body\nend\n']
Path('original.ml').write_text(''.join(out))
Path('current.ml').write_bytes(Path('native/main.assembly').read_bytes())
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cat >check.ml <<'ML'
let require n b=if not b then failwith n
let collect()=Gc.full_major();Gc.full_major()
module Original_build()=Original.Make(Target)
module Current_build()=Current.Make(Target)
let ()=
 Target.trace:=[];let module Old=Original_build()in let old_trace=List.rev !Target.trace in
 Target.trace:=[];let module New=Current_build()in
 require "single ordered preparation"(old_trace=["prepare"]&&old_trace=List.rev !Target.trace&& !Target.prepared=2);
 let text=String.make 1048576 't' in let ints=[1;2;3]and strings=[text]in
 require "original alias values"(New.id strings==strings&&New.first text==text);
 require "same function reexport"(New.first==New.second);
 let owner,run=New.bundle and old_owner,old_run=Old.bundle in
 let pending,wake=Lwt.task()in Target.response:=pending;
 let seen=ref []in Target.observe:=(fun held value->seen:=(held==owner,value==text,Lwt.get Target.context):: !seen);
 require "original promise and argument context"(Lwt.with_value Target.context(Some "caller")(fun()->run text)==pending);
 require "original owned value and input"(!seen=[true,true,Some "caller"]);
 let allocation f=Gc.full_major();let n=Gc.allocated_bytes()in for _=1 to 1000 do ignore(f text)done;Gc.allocated_bytes()-.n in
 Target.observe:=(fun _ _->());require "exact call allocation"(allocation run=allocation old_run);
 Lwt.cancel pending;require "cancellation original promise"(Lwt.state pending=Lwt.Fail Lwt.Canceled);
 let exact=Failure "callback"in Target.observe:=(fun _ _->raise exact);
 require "synchronous exception identity"(try ignore(run text);false with e->e==exact);
 Target.observe:=(fun _ _->());Target.fail_prepare:=true;
 require "initialization exception identity"(try let module Bad=Current_build()in ignore Bad.bundle;false with e->e==Target.failure);
 Target.fail_prepare:=false;
 let retained()=let module M=Current_build()in let _,run=M.bundle in collect();require "live owner retained"(Weak.check Target.weak 0);ignore(run "alive")in
 retained();collect();require "owner naturally released"(not(Weak.check Target.weak 0));
 ignore(old_owner,owner,wake);
 print_endline "PASS: abstract functor/callable scope, original aliases, initialization, physical identity, context/promise/fault phases, exact call allocation and natural Weak ownership"
ML
for mode in native bytecode;do
 if [ "$mode" = native ];then compiler=ocamlopt;else compiler=ocamlc;fi
 ocamlfind "$compiler" -w -a -package lwt.unix -linkpkg uint63.ml soma_word64.ml float64.ml soma_nat.ml soma_effect.ml soma_handles.ml target.ml original.ml current.ml check.ml -o "check-$mode" >"$mode.log" 2>&1
 ./"check-$mode"
done
# Editing a declaration's open changes the checked main/layout identity.
sed -i.bak 's/Open \["Target"\] Functor/Functor/' main.soma
soma hash main.soma -no-soma-prelude >changed-hash.log
python3 - <<'PY'
from pathlib import Path
before=next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]=='main.main')
after=next(l.split()[0]for l in Path('changed-hash.log').read_text().splitlines()if l.split()[2]=='main.main')
assert before!=after
PY
printf '%s\n' 'PASS: lexical scope provenance, invalid declarations and semantic identity'
