#!/usr/bin/env bash
# Checked scope modules and binding operators borrow unrestricted generic values.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 20 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
let bind=Lwt.bind
let identity x=x
let context:string Lwt.key=Lwt.new_key()
let fault=Failure "publication frame"
ML
cat >scope.definition <<'SOMA'
From Soma Require Import Native Handles.
OCaml Native External Value target : forall A B:Type,promise A -> (A -> promise B) -> promise B := "Target.bind".
OCaml Native External Value same : forall A:Type,A -> A := "Target.identity".
OCaml Native Reexport Value bind := target.
OCaml Native Reexport Value identity := same.
SOMA
cat >other.definition <<'SOMA'
From Soma Require Import Native Handles.
OCaml Native External Value same : forall A:Type,A -> A := "Target.identity".
OCaml Native Reexport Value identity := same.
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import scope other.
Definition main:=scope.bind.
SOMA
cat >main.exp <<'SOMA'
Theorem marker_is_canonical:scope.bind=tt.
Proof. reflexivity. Qed.
SOMA
soma extract main.soma -no-soma-prelude -o baseline >baseline.log 2>&1
soma hash main.soma -no-soma-prelude >baseline-hash.log
python3 - <<'PY'
from pathlib import Path
import shlex,hashlib
rows=[shlex.split(l)for l in Path('baseline/native_value_reexports.manifest').read_text().splitlines()[1:]]
rows=[r for r in rows if r[1]=='scope'];assert len(rows)==2 and [r[6]for r in rows]==['bind','identity']
assert len({r[4]for r in rows})==1
fragment=Path('baseline/'+rows[0][4]).read_bytes();assert hashlib.sha256(fragment).hexdigest()==rows[0][5]
Path('before.ml').write_bytes(b'module Checked = struct\n'+fragment+b'end\nlet ( let* ) = Checked.bind\nlet ( and+ ) = Checked.identity\n')
Path('before.mli').write_text("module Checked:sig\nval bind:'a Lwt.t -> ('a -> 'b Lwt.t) -> 'b Lwt.t\nval identity:'a -> 'a\nend\nval (let*):'a Lwt.t -> ('a -> 'b Lwt.t) -> 'b Lwt.t\nval (and+):'a -> 'a\n")
PY
cat >>main.soma <<'SOMA'
Fail OCaml Native Publication Frame scope.bind From scope.bind As "Checked" With [Operator "let*" := scope.bind].
Fail OCaml Native Publication Frame main From other.identity As "Checked" With [Operator "let*" := other.identity].
Fail OCaml Native Publication Frame main From scope.bind As "lowercase" With [Operator "let*" := scope.bind].
Fail OCaml Native Publication Frame main From scope.bind As "Checked.Bad" With [Operator "let*" := scope.bind].
Fail OCaml Native Publication Frame main From scope.bind As "Soma_values_bad" With [Operator "let*" := scope.bind].
Fail OCaml Native Publication Frame main From scope.bind As "Checked" With [Operator "let*;code" := scope.bind].
Fail OCaml Native Publication Frame main From scope.bind As "Checked" With [Operator "let*" := other.identity].
Fail OCaml Native Publication Frame main From scope.bind As "Checked" With [Operator "let*" := scope.bind;Operator "let*" := scope.identity].
OCaml Native Publication Frame main From scope.bind As "Checked"
 With [Operator "let*" := scope.bind;Operator "and+" := scope.identity].
Fail OCaml Native Publication Frame main From scope.bind As "Again" With [Operator "let*" := scope.bind].
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
def proof(path,name):return next(l.split()[:2]for l in Path(path).read_text().splitlines()if l.split()[2]==name)
assert proof('baseline-hash.log','main.marker_is_canonical')==proof('hash.log','main.marker_is_canonical')
Path('after.ml').write_bytes(Path('native/main.assembly').read_bytes());Path('after.mli').write_bytes(Path('native/main.assembly-interface').read_bytes())
assert Path('after.ml').read_bytes()==Path('before.ml').read_bytes()
for side in ['before','after']:Path(side+'_build.ml').write_text('module Make()=struct\n'+Path(side+'.ml').read_text()+'\nend\n')
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cat >check.ml <<'ML'
module A(X:module type of Before)=struct end
module B(X:module type of After)=struct end
module AB=A(After)
module BA=B(Before)
let[@inline never] allocated f=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 1000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.start
let ()=
 assert(After.Checked.bind==Lwt.bind&&After.(let*)==Lwt.bind&&After.Checked.identity==Target.identity&&After.(and+)==Target.identity);
 let bytes=Bytes.make 8 'g'in assert(After.Checked.identity bytes==bytes&&After.Checked.identity true&&After.(and+) "generic"="generic");
 let check bind=
  let input,wake=Lwt.task()in let observed=ref false in
  let result=Lwt.with_value Target.context(Some "caller")(fun()->bind input(fun value->assert(value==bytes&&Lwt.get Target.context=Some "caller");observed:=true;Lwt.return value))in
  assert(Lwt.state result=Lwt.Sleep);Lwt.wakeup wake bytes;
  assert(!observed&&match Lwt.state result with Lwt.Return value->value==bytes|_->false);
  let pending,_=Lwt.task()in let result=bind pending(fun _->Lwt.return bytes)in Lwt.cancel result;assert(Lwt.state pending=Lwt.Fail Lwt.Canceled);
  let failed=bind(Lwt.fail Target.fault)(fun _->Lwt.return bytes)in(match Lwt.state failed with Lwt.Fail ex->assert(ex==Target.fault)|_->assert false)
 in check Before.(let*);check After.(let*);
 let before=allocated(fun()->let module M=Before_build.Make()in M.(let*))in
 let after=allocated(fun()->let module M=After_build.Make()in M.(let*))in assert(before=after);
 let run bind=allocated(fun()->bind(Lwt.return bytes)(fun value->Lwt.return value))in assert(run Before.(let*)=run After.(let*));
 let lifetime bind=
  let weak=Weak.create 1 in
  let[@inline never] create()=let value=Bytes.make 65536 'w'in Weak.set weak 0(Some value);let p,w=Lwt.task()in
    let result=bind p(fun()->Lwt.return value)in Gc.full_major();assert(Weak.check weak 0);ignore(Sys.opaque_identity w);result in
  let[@inline never] cancel()=let result=create()in Lwt.cancel result in
  cancel();Gc.full_major();Weak.check weak 0 in
 assert(not(lifetime Before.(let*)));assert(not(lifetime After.(let*)));
 Printf.printf "publication frames: full generic module/operator APIs, original functions/context/fault/cancel, exact init %.0f/call allocation and natural Weak passed\n%!"after
ML
for backend in ocamlopt ocamlc;do
 rm -f ./*.cm[iox] ./*.o
 ocamlfind "$backend" -w -a -package lwt.unix -linkpkg soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml before.mli before.ml after.mli after.ml before_build.ml after_build.ml check.ml -o check
 ./check
 done
cp main.soma original
sed 's/As "Checked"/As "CheckedAgain"/g' original >main.soma
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
cp original main.soma
cat >proxy.soma <<'SOMA'
Import main.
Definition main:=scope.bind.
SOMA
soma extract proxy.soma -no-soma-prelude -o proxy-native >proxy.log 2>&1
 test ! -f proxy-native/native_assemblies.manifest
python3 - <<'PY'
from pathlib import Path
p=Path('main.soma');s=p.read_text();s=s[:s.index('Fail OCaml Native Publication Frame')];p.write_text(s)
PY
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
 test ! -f native/native_assemblies.manifest
 test ! -f native/main.assembly
 test ! -f native/main.assembly-interface
