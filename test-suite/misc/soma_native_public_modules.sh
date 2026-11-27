#!/usr/bin/env bash
# Flat aliases publish the complete original canonical modules, including exceptions.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 25 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
let count=ref 0
let weak=Weak.create 1
let fail=ref false
let fault=Failure "public modules"
let create()=incr count;if !fail then raise fault;let v=Bytes.make 65536 'x'in Weak.set weak 0(Some v);v
ML
cat >schema.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
OCaml Native Algebraic graph := [
 data := {mutable active:bool; next:option node};
 node := ["Empty";"Next" Of [data]]
] Exceptions ["EmptyGraph";"Bad" Of [PrimInt63.int]].
OCaml Native Immutable Record settings := {secret:buffer;active:bool}.
OCaml Native Build make : buffer -> bool -> settings := "secret" "active".
OCaml Native External Callback create : unit -> buffer := "Target.create".
OCaml Native External Type borrowed := "Bytes.t".
OCaml Native Record unused := {unused_value:bool}.
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import schema.
Definition prepared:=Native.Export(Native.Bind(Native.Call_callback create tt)(fun bytes=>Native.Call_callback make(bytes,true))).
Definition borrow(value:data):=value.
Definition borrow_node(value:node):=value.
Definition borrow_external(value:borrowed):=value.
Definition keep{A:Type}(value:A):=value.
Definition main:=(prepared,(borrow,borrow_node,borrow_external,@keep)).
Fail OCaml Native Public Modules prepared With [Module "Layout" := schema.data].
Fail OCaml Native Public Modules main With [Value "Layout" := schema.data].
Fail OCaml Native Public Modules main With [Module "lowercase" := schema.data].
Fail OCaml Native Public Modules main With [Module "Layout.X" := schema.data].
Fail OCaml Native Public Modules main With [Module "Soma_owned_bad" := schema.data].
Fail OCaml Native Public Modules main With [Module "Layout;code" := schema.data].
Fail OCaml Native Public Modules main With [Module "Layout" := schema.data;Module "Layout" := schema.settings].
Fail OCaml Native Public Modules main With [Module "Unused" := schema.unused].
Fail OCaml Native Public Modules main With [Module "Wrong" := schema.create].
Fail OCaml Native Public Modules main With [Module "External" := schema.borrowed].
OCaml Native Public Modules main With [Module "Layout" := schema.node;Module "Settings" := schema.settings].
Fail OCaml Native Public Modules main With [Module "Again" := schema.data].
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
rows=Path('native/native_assemblies.manifest').read_text().splitlines();assert len(rows)==3
for row in rows[1:]:
 symbol,source,src,file,digest,program,interface,bindings,layout,contract=shlex.split(row)
 for path,h in [(source,src),('native/'+file,digest),('native/prog.ml',program),('native/prog.mli',interface),('native/soma_bindings.ml',bindings)]:assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==h
 assert next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]==symbol)==contract
for l in Path('hash.log').read_text().splitlines():
 assert '  assumes 'not in l or set(l.split('  assumes ',1)[1].split(', '))<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'}
# Reproduce the old emitter only in this independent test, over the complete
# fresh program and the original byte-authenticated canonical schema products.
def canonical(manifest,symbol):
 rows=[shlex.split(l)for l in Path('native/'+manifest).read_text().splitlines()[1:]]
 row=next(r for r in rows if r[0]==symbol)
 assert hashlib.sha256(Path('native/'+row[3]).read_bytes()).hexdigest()==row[4]
 return Path(row[3]).stem.capitalize()
graph=canonical('native_algebraic.manifest','schema.data');settings=canonical('native_owned.manifest','schema.settings')
prefix='module Layout = '+graph+'\nmodule Settings = '+settings+'\n'
for suffix in ['.ml','.mli']:
 Path('before'+suffix).write_text(prefix+Path('native/prog'+suffix).read_text())
Path('after.ml').write_bytes(Path('native/main.assembly').read_bytes())
Path('after.mli').write_bytes(Path('native/main.assembly-interface').read_bytes())
assert prefix in Path('after.ml').read_text() and prefix in Path('after.mli').read_text()
for side in ['before','after']:
 Path(side+'_build.ml').write_text('module Make()=struct\n'+Path(side+'.ml').read_text()+'\nend\n')
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
 let data:Before.Layout.data={active=true;next=None}in
 let same:After.Layout.data=data in assert(data==same);same.active<-false;assert(not data.active);
 let next=Before.Layout.Next data in let same:After.Layout.node=next in
 (match same with After.Layout.Next value->assert(value==data)|_->assert false);
 assert(After.borrow data==data&&Before.borrow data==data);
 let exception_from_old=Before.Layout.Bad 7 in
 (try raise exception_from_old with After.Layout.Bad code->assert(code=7)|_->assert false);
 assert(Before.Layout.EmptyGraph==After.Layout.EmptyGraph);
 assert(Before.Settings.soma_get_secret Before.prepared==Before.prepared.secret);
 assert(After.Settings.soma_get_secret After.prepared==After.prepared.secret);
 let settings:After.Settings.t=Before.prepared in assert(settings==Before.prepared);
 let generic=Bytes.make 8 'g'in assert(After.keep generic==generic&&After.keep true&&Before.keep "hello"="hello");
 let before=allocated(fun()->let module M=Before_build.Make()in M.prepared)in
 let after=allocated(fun()->let module M=After_build.Make()in M.prepared)in assert(before=after);
 let lifetime make=
  let[@inline never] retain()=let value=make()in Gc.full_major();assert(Weak.check Target.weak 0);ignore(Sys.opaque_identity value)in
  retain();Gc.full_major();Weak.check Target.weak 0 in
 let[@inline never] old()=let module M=Before_build.Make()in M.prepared in
 let[@inline never] fresh()=let module M=After_build.Make()in M.prepared in
 assert(not(lifetime old));assert(not(lifetime fresh));
 Target.fail:=true;(try let module M=After_build.Make()in ignore M.prepared;assert false with ex->assert(ex==Target.fault));
 Printf.printf "public modules: complete API, canonical records/constructors/exceptions/getters, exact init allocation %.0f, natural Weak lifetime passed\n%!"after
ML
for backend in ocamlopt ocamlc;do
 rm -f ./*.cm[iox] ./*.o
 ocamlfind "$backend" -w -a -package lwt.unix -linkpkg -I native soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml native/soma_algebraic_*.ml native/soma_owned_*.ml soma_bindings.ml before.mli before.ml after.mli after.ml before_build.ml after_build.ml check.ml -o check
 ./check
 done
cp main.soma original
# The owner main changes identity with its requested module names; raw runtime
# code and canonical native units do not change.
sed 's/Module "Settings" := schema.settings/Module "Configuration" := schema.settings/' original >main.soma
soma extract main.soma -no-soma-prelude -o renamed >renamed.log 2>&1
soma hash main.soma -no-soma-prelude >renamed-hash.log
python3 - <<'PY'
from pathlib import Path
old=next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]=='main.main')
new=next(l.split()[0]for l in Path('renamed-hash.log').read_text().splitlines()if l.split()[2]=='main.main')
assert old!=new
for suffix in ['.ml','.mli']:assert Path('native/prog'+suffix).read_bytes()==Path('renamed/prog'+suffix).read_bytes()
for p in Path('native').glob('soma_algebraic_*.ml'):assert p.read_bytes()==(Path('renamed')/p.name).read_bytes()
for p in Path('native').glob('soma_owned_*.ml'):assert p.read_bytes()==(Path('renamed')/p.name).read_bytes()
PY
cp original main.soma
cat >proxy.soma <<'SOMA'
Import main.
Definition main:=main.prepared.
SOMA
soma extract proxy.soma -no-soma-prelude -o proxy-native >proxy.log 2>&1
 test ! -f proxy-native/native_assemblies.manifest
python3 - <<'PY'
from pathlib import Path
p=Path('main.soma');s=p.read_text();s=s[:s.index('Fail OCaml Native Public Modules')];p.write_text(s)
PY
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
 test ! -f native/main.assembly
 test ! -f native/main.assembly-interface
 test ! -f native/native_assemblies.manifest
