#!/usr/bin/env bash
# Complete canonical schemas replace an alias without changing runtime code.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 20 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >schema.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native Algebraic network := [
 flow := {bytes:buffer;run:string -> promise string};
 t := {flow:flow;current:unit -> flow;mutable count:PrimInt63.int};
 status := ["Ready";"Data" Of [string]]
].
OCaml Native Algebraic unused := [other := {flag:bool}].
OCaml Native External Type plain := "Target.t".
SOMA
cat >target.definition <<'SOMA'
From Soma Require Import Native Handles.
Import schema.
OCaml Native External Callback create : unit -> t := "Target.create".
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import schema target.
Definition bindings:=Native.Export(Native.Call_callback create tt).
Definition keep{A:Type}(value:A):=value.
Definition main:=(bindings,@keep).
SOMA
soma extract main.soma -no-soma-prelude -o baseline >baseline.log 2>&1
soma hash main.soma -no-soma-prelude >baseline-hash.log
# The independent former Kykeon algorithm is restricted to this test oracle.
python3 - <<'PY'
from pathlib import Path
import shlex,re
row=shlex.split(Path('baseline/native_algebraic.manifest').read_text().splitlines()[1]);owner=Path(row[3]).stem.capitalize()
for suffix,statement in [('.ml','include '+owner),('.mli','include module type of struct include '+owner+' end')]:
 text,count=re.subn(r'^type t =\s+'+owner+r'\.t\n','',Path('baseline/prog'+suffix).read_text(),flags=re.M)
 assert count==1
 Path('before'+suffix).write_text(statement+'\n'+text)
Path('target.ml').write_text('module Storage='+owner+'''\n
let count=ref 0
let weak=Weak.create 1
let fail=ref false
let fault=Failure "canonical include"
let context:string Lwt.key=Lwt.new_key()
let response=ref(Lwt.return "ready")
let observe=ref(fun (_:bytes) (_:string)->())
let create()=incr count;if !fail then raise fault;
 let bytes=Bytes.make 65536 'x'in
 let run text=(!observe)bytes text;!response in
 let flow:Storage.flow={bytes;run}in
 let value:Storage.t={flow;current=(fun()->flow);count=0}in
 Weak.set weak 0(Some value);value
''')
PY
cat >>main.soma <<'SOMA'
Fail OCaml Native Canonical Include bindings From schema.t.
Fail OCaml Native Canonical Include main From schema.other.
Fail OCaml Native Canonical Include main From schema.plain.
Fail OCaml Native Canonical Include main From target.create.
OCaml Native Canonical Include main From schema.t.
Fail OCaml Native Canonical Include main From schema.t.
Fail OCaml Native Canonical Include main From schema.flow.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
lines=Path('native/native_canonical_includes.manifest').read_text().splitlines();assert lines[0]=='soma-native-canonical-includes-v1'and len(lines)==2
owner,source,src,symbol,member,target,schema,ml,mli,identity=shlex.split(lines[1])
assert(owner,symbol,member)==('main.main','schema.t','t')
for path,h in [(source,src),('native/'+target[0].lower()+target[1:]+'.ml',schema),('native/prog.ml',ml),('native/prog.mli',mli)]:
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==h
abis=[shlex.split(l)for l in Path('native/native_abi.manifest').read_text().splitlines()[1:]]
assert any(o==owner and h==src and hashlib.sha256(i.replace('\\n','\n').encode()).hexdigest()==identity for o,_,h,i in abis)
for path in ['baseline-hash.log','hash.log']:
 for line in Path(path).read_text().splitlines():assert '  assumes 'not in line or line.split('  assumes ',1)[1]=='Corelib.Numbers.Cyclic.Int63.PrimInt63.int'
def mainhash(path):return next(l.split()[0]for l in Path(path).read_text().splitlines()if l.split()[2]=='main.main')
assert mainhash('baseline-hash.log')!=mainhash('hash.log')
for suffix in ['.ml','.mli']:Path('after'+suffix).write_bytes(Path('native/prog'+suffix).read_bytes())
for side in ['before','after']:Path(side+'_build.ml').write_text('module Make()=struct\n'+Path(side+'.ml').read_text()+'\nend\n')
PY
cat >ast.ml <<'ML'
let ()=
 let parse path signature=let channel=open_in path in Fun.protect ~finally:(fun()->close_in channel)(fun()->
  let lex=Lexing.from_channel channel in
  if signature then Format.asprintf "%a" Pprintast.signature(Parse.interface lex)
  else Format.asprintf "%a" Pprintast.structure(Parse.implementation lex))in
 List.iter(fun signature->let suffix=if signature then ".mli"else ".ml"in
  assert(parse("before"^suffix)signature=parse("after"^suffix)signature))[false;true];
 print_endline "PASS: complete implementation/interface ASTs identical; no omissions or normalizations"
ML
ocamlfind ocamlc -package compiler-libs.common -linkpkg ast.ml -o ast >ast.log 2>&1
./ast
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_bindings.ml} .
cat >check.ml <<'ML'
module A(X:module type of Before)=struct end
module B(X:module type of After)=struct end
module AB=A(After)
module BA=B(Before)
let[@inline never] allocated f=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 1000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.start
let ()=
 assert(!Target.count=2);
 let old=Before.bindings and fresh=After.bindings in
 let check(owner:After.t)=
  assert(owner.current()==owner.flow);
  owner.count<-max_int;assert(owner.count=max_int);
  let pending,_=Lwt.task()in Target.response:=pending;
  Target.observe:=(fun bytes text->assert(bytes==owner.flow.bytes&&text="hello"&&Lwt.get Target.context=Some "caller"));
  assert(Lwt.with_value Target.context(Some "caller")(fun()->owner.flow.run "hello")==pending);
  Target.observe:=(fun _ _->raise Target.fault);
  (try ignore(owner.flow.run "fault");assert false with ex->assert(ex==Target.fault));
  Target.observe:=(fun _ _->());assert(owner.flow.run "cancel"==pending);Lwt.cancel pending;assert(Lwt.state pending=Lwt.Fail Lwt.Canceled)
 in check old;check fresh;
 let alias:After.t=old in assert(alias==old&&alias.flow==old.flow&&alias.current==old.current);
 let status:After.status=Before.Data "borrowed"in(match status with Target.Storage.Data text->assert(text="borrowed")|_->assert false);
 assert((After.Ready:Target.Storage.status)=Before.Ready);
 let bytes=Bytes.make 8 'g'in assert(After.keep bytes==bytes&&After.keep true&&Before.keep "generic"="generic");
 let before=allocated(fun()->let module M=Before_build.Make()in M.bindings)in
 let after=allocated(fun()->let module M=After_build.Make()in M.bindings)in assert(before=after);
 assert(allocated(fun()->old.flow.run "call")=allocated(fun()->fresh.flow.run "call"));
 let lifetime make=
  let[@inline never] retain()=let owner=make()in Gc.full_major();assert(Weak.check Target.weak 0);ignore(Sys.opaque_identity owner)in
  retain();Gc.full_major();Weak.check Target.weak 0 in
 let[@inline never] old()=let module M=Before_build.Make()in M.bindings in
 let[@inline never] fresh()=let module M=After_build.Make()in M.bindings in
 assert(not(lifetime old));assert(not(lifetime fresh));
 Target.fail:=true;(try let module M=After_build.Make()in ignore M.bindings;assert false with ex->assert(ex==Target.fault));
 Printf.printf "canonical includes: complete reciprocal APIs/types/constructors, original objects/promise/context/fault/cancel, exact init %.0f, call allocation and natural Weak passed\n%!"after
ML
for backend in ocamlopt ocamlc;do
 rm -f ./*.cm[iox] ./*.o
 schemas=$(find native -name 'soma_algebraic_*.ml' -print)
 ocamlfind "$backend" -w -a -package lwt.unix -linkpkg -I native soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml $schemas target.ml soma_bindings.ml before.mli before.ml after.mli after.ml before_build.ml after_build.ml check.ml -o check
 ./check
done
cp main.soma original
cat >proxy.soma <<'SOMA'
Import main.
Definition main:=main.bindings.
SOMA
soma extract proxy.soma -no-soma-prelude -o proxy-native >proxy.log 2>&1
test ! -f proxy-native/native_canonical_includes.manifest
# A second extracted alias for a member must not shadow the complete include.
sed '/OCaml Native Canonical Include/d' original >main.soma
cat >>main.soma <<'SOMA'
Definition another:=Native.Return(None:option schema.flow).
Definition main2:=(main,another).
SOMA
# Use the actual entrypoint: the additional alias is now part of its graph.
python3 - <<'PY'
from pathlib import Path
p=Path('main.soma');s=p.read_text().replace('Definition main:=(bindings,@keep).','Definition original:=(bindings,@keep).').replace('Definition main2:=(main,another).','Definition main:=(original,another).')
p.write_text(s+'OCaml Native Canonical Include main From schema.t.\n')
PY
if soma extract main.soma -no-soma-prelude -o collision >collision.log 2>&1;then echo 'accepted a conflicting schema alias' >&2;exit 1;fi
rg -q 'canonical include conflicts|canonical type name' collision.log
# Metadata disappears when its Source declaration is removed.
sed '/OCaml Native Canonical Include/d' original >main.soma
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
test ! -f native/native_canonical_includes.manifest
