#!/usr/bin/env bash
# Direct checked exports preserve compiler closure approximations and ownership.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/{extract,build}.log 2>/dev/null || true; fi; if [ "${KEEP:-0}" = 1 ]; then echo "Retained $work"; else rm -rf "$work"; fi; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
type box={contents:bytes option}
let owner:bytes option ref=ref None
let fault=Failure "export leaf"
let fail=ref false
let context:string Lwt.key=Lwt.new_key()
let seen=ref None
let leaf owner promise=seen:=Lwt.get context;Option.iter(fun bytes->ignore(Bytes.length bytes))!owner;if !fail then raise fault;promise
let immediate=Lwt.return
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native External Value marker : unit := "Stdlib.ignore" With "unused".
SOMA
cat > functions.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
OCaml Native External Type bytes := "Bytes.t".
OCaml Native External Value returned : forall A:Type,A -> promise A := "Lwt.return".
OCaml Native External Value bound : forall A B:Type,promise A -> (A -> promise B) -> promise B := "Lwt.bind".
OCaml Native External Value leaf : forall A:Type,reference(option bytes) -> promise A -> promise A := "Target.leaf".
OCaml Native External Value owner : reference(option bytes) := "Target.owner".
OCaml Native Static Invoke prepared_ret : forall A:Type,A -> promise A := returned With [Argument 0] AtFullApplication.
OCaml Native Static Invoke prepared_kept : forall A:Type,promise A -> promise A := leaf With [Value owner;Argument 0] AtFullApplication.
OCaml Native Reexport Value ret := prepared_ret.
OCaml Native Reexport Value bind := bound.
OCaml Native Reexport Value kept := prepared_kept.
OCaml Native External Value scalar : PrimInt63.int := "Stdlib.max_int".
Fail OCaml Native Reexport Value invalid_scalar := scalar.
Fail OCaml Native Reexport Value invalid_source := tt.
OCaml Native External Type box := "Target.box".
OCaml Native Get direct : box -> option bytes := "contents".
Fail OCaml Native Reexport Value invalid_get := direct.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target functions.
Definition main := (ret,bind,kept,Native.Export(Native.Call_callback marker tt)).
SOMA
cat > main.exp <<'SOMA'
Theorem exports_are_canonical : ret=tt /\ bind=tt /\ kept=tt.
Proof. repeat split;reflexivity. Qed.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >before-hash
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
lines=Path('native/native_value_reexports.manifest').read_text().splitlines();assert lines[0]=='soma-native-value-reexports-v1'
rows=[shlex.split(line)for line in lines[1:]];assert len(rows)==3
assert [row[6]for row in rows]==['ret','bind','kept']
assert [row[8]for row in rows]==['0','1','2']
for symbol,namespace,source,source_hash,filename,digest,name,owner,order in rows:
 assert symbol==namespace+'.'+name and hashlib.sha256(Path(source).read_bytes()).hexdigest()==source_hash
 assert Path(filename).name==filename and hashlib.sha256(Path('native',filename).read_bytes()).hexdigest()==digest
Path('raw.ml').write_bytes(Path('native',rows[0][4]).read_bytes())
assert 'Lwt.return bound0'in Path('raw.ml').read_text()
assert 'Lwt.bind'in Path('raw.ml').read_text()
assert all('  assumes 'not in line for line in Path('before-hash').read_text().splitlines()if ' functions.ret'in line or ' main.exports_are_canonical'in line)
Path('scope.ml').write_text('include Soma_bindings.'+Path(rows[0][4]).stem.capitalize()+'\n')
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_bindings.mli,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cat > original.ml <<'ML'
let ret value=Lwt.return value
let bind=Lwt.bind
let kept promise=Target.leaf Target.owner promise
ML
cat > check.ml <<'ML'
let require name value=if not value then failwith name
module Original()=struct
 let ret value=Lwt.return value
 let bind=Lwt.bind
 let allocations()=let measure fn=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.start in
  measure(fun()->ret 7),measure(fun()->bind(ret 7)(fun n->ret(n+1)))
end
module Current()=struct
 include Raw
 let allocations()=let measure fn=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.start in
  measure(fun()->ret 7),measure(fun()->bind(ret 7)(fun n->ret(n+1)))
end
module O=Original()
module N=Current()
let graph ret=
 let weak=Weak.create 1 in
 let[@inline never] prepare()=let bytes=Bytes.make 4096(Sys.opaque_identity 'x')in Weak.set weak 0(Some bytes);ret bytes in
 let[@inline never] hold()=let promise=prepare()in Gc.full_major();Gc.full_major();require "promise retains original payload"(Weak.check weak 0);ignore(Sys.opaque_identity promise)in
 hold();Gc.full_major();Gc.full_major();require "dropped promise releases payload"(not(Weak.check weak 0))
let ()=
 require "borrowed bind function identities"(Raw.bind==Lwt.bind&&Scope.bind==Lwt.bind);
 let bytes=Bytes.of_string "payload"and callback()=37 in
 require "generic returned bytes"(match Lwt.state(Raw.ret bytes)with Lwt.Return value->value==bytes|_->false);
 require "generic returned function"(match Lwt.state(Raw.ret callback)with Lwt.Return value->value==callback|_->false);
 require "independently generic bind domains"(Lwt.state(Raw.bind(Raw.ret 7)(fun n->Raw.ret(string_of_int n)))=Lwt.Return "7");
 let promise,_=Lwt.task()in
 Lwt.with_value Target.context(Some "caller")(fun()->require "same promise and caller context"(Raw.kept promise==promise&&Scope.kept promise==promise&& !Target.seen=Some"caller"));
 Lwt.cancel promise;require "cancel original promise"(match Lwt.state promise with Lwt.Fail Lwt.Canceled->true|_->false);
 Target.fail:=true;require "exact leaf exception"(try ignore(Raw.kept(Lwt.return()));false with error->error==Target.fault);Target.fail:=false;
 let weak=Weak.create 1 in
 let[@inline never] install()=let bytes=Bytes.make 32(Sys.opaque_identity 'b')in Weak.set weak 0(Some bytes);Target.owner:=Some bytes in
 install();ignore(Raw.kept(Lwt.return()));Gc.full_major();require "live owner payload"(Weak.check weak 0);
 Target.owner:=None;Gc.full_major();Gc.full_major();require "no snapshot of owner payload"(not(Weak.check weak 0));
 graph O.ret;graph Raw.ret;graph Scope.ret;
 let module O2=Original()in let module N2=Current()in require "native/bytecode closed sharing"((O.ret==O2.ret)=(N.ret==N2.ret));
 let old=O.allocations()and current=N.allocations()in require "exact allocation including consumer callback closure"(old=current);
 let a,b=old in Printf.printf "PASS: typed native value exports preserve closed sharing, borrowed function identity, generic values, promises/context/cancel, exact faults, natural Weak owners and consumer callback allocation %.0f/%.0f B.\n%!"a b
ML
python3 - <<'PYEMBED'
from pathlib import Path
p=Path('check.ml');p.write_text(p.read_text().replace(' include Raw\n',Path('raw.ml').read_text()))
PYEMBED
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_bindings.mli soma_bindings.ml prog.mli prog.ml raw.ml scope.ml original.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
sed -i.bak 's/"Lwt.return"/"Target.immediate"/' functions.definition
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash
if cmp -s before-abi changed/native_abi.manifest;then echo 'native value ABI did not change' >&2;exit 1;fi
python3 - <<'PY'
from pathlib import Path
rows=lambda text:[line for line in text.splitlines()if len(line.split())>=3 and line.split()[2]=='main.main']
a=rows(Path('before-hash').read_text());b=rows(Path('changed-hash').read_text());assert a and b and a!=b
PY
