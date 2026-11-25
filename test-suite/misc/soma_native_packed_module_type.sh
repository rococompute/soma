#!/usr/bin/env bash
# Named module packages stay opaque logically and retain exact native values.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/{extract,build}.log 2>/dev/null || true; fi; if [ "${KEEP:-0}" = 1 ]; then echo "Retained $work"; else rm -rf "$work"; fi; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
module type API=sig
 type t
 val value:t
 val read:t->bytes
 val identity:'a->'a
 val slot:bytes option ref
 exception Fault of bytes
 val context:string Lwt.key
 val pending:unit->bytes Lwt.t
end
let initialized=ref 0
let fault=Failure "package constructor"
let fail=ref false
let construct bytes promise =
 if !fail then raise fault;
 incr initialized;
 (module struct
  type t=bytes
  let value=bytes
  let read value=value
  let identity value=value
  let slot=ref(Some bytes)
  exception Fault of bytes
  let context=Lwt.new_key()
  let pending()=if Lwt.get context<>Some"caller"then failwith"context";promise
 end:API)
let marker=()
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native External Value marker : unit := "Target.marker".
SOMA
cat > package.definition <<'SOMA'
From Soma Require Import Native Handles.
OCaml Native External Type bytes := "Bytes.t".
OCaml Native Packed Module Type api := "Target.API".
OCaml Native External Value build : bytes -> promise bytes -> api := "Target.construct".
OCaml Native Reexport Value construct := build.
Fail OCaml Native Packed Module Type invalid := "Target.api".
Fail OCaml Native Packed Module Type invalid := "Target..API".
Fail OCaml Native Packed Module Type invalid := "Target.API; let x=1".
Fail OCaml Native Packed Module Type invalid := "Target.Make(Arg)".
Fail OCaml Native Packed Module Type invalid := "Target.API with type t=int".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target package.
Definition identity(value:api) := value.
Definition main := (identity,construct,Native.Export(Native.Call_callback marker tt)).
SOMA
cat > main.exp <<'SOMA'
Theorem package_export_is_canonical : construct=tt.
Proof. reflexivity. Qed.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >before-hash
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_bindings.mli,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
python3 - <<'PY'
from pathlib import Path
import shlex
rows=Path('native/native_value_reexports.manifest').read_text().splitlines()
row=shlex.split(rows[1]);Path('raw.ml').write_bytes(Path('native',row[4]).read_bytes())
assert 'type api = (module Target.API)'in Path('prog.mli').read_text()
assert '(module Target.API)'in Path('soma_bindings.mli').read_text()
Path('scope.ml').write_text('include Soma_bindings.'+Path(row[4]).stem.capitalize()+'\n')
PY
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let graph construct=
 let weak=Weak.create 1 in
 let[@inline never] prepare()=let bytes=Bytes.make 4096(Sys.opaque_identity 'x')in Weak.set weak 0(Some bytes);construct bytes(Lwt.return bytes)in
 let[@inline never] hold()=let packed=prepare()in Gc.full_major();Gc.full_major();require "package retains payload owner"(Weak.check weak 0);ignore(Sys.opaque_identity packed)in
 hold();Gc.full_major();Gc.full_major();require "dropped package releases payload owner"(not(Weak.check weak 0))
let ()=
 require "borrowed constructor function"(Raw.construct==Target.construct&&Scope.construct==Target.construct);
 let bytes=Bytes.of_string "payload"in let promise,_=Lwt.task()in
 let packed=Raw.construct bytes promise in
 require "logical identity preserves physical package"(Prog.identity packed==packed);
 let module P=(val Prog.identity packed:Target.API)in
 require "unpacked abstract value retains original buffer"(P.read P.value==bytes);
 require "mutable state retained"(match !P.slot with Some value->value==bytes|_->false);
 P.slot:=None;require "same package exposes same ref"(let module Q=(val packed:Target.API)in Q.slot==P.slot&& !Q.slot=None);
 let callback()=37 in require "generic module member"(P.identity callback==callback&&P.identity bytes==bytes);
 let module Q=(val packed:Target.API)in
 require "function and exception constructor identities"(P.identity==Q.identity&&try raise(P.Fault bytes)with Q.Fault value->value==bytes);
 Lwt.with_value P.context(Some"caller")(fun()->require "same pending promise/context"(P.pending()==promise));
 Lwt.cancel promise;require "original cancellation"(match Lwt.state promise with Lwt.Fail Lwt.Canceled->true|_->false);
 Target.fail:=true;require "exact constructor exception"(try ignore(Raw.construct bytes(Lwt.return bytes));false with error->error==Target.fault);Target.fail:=false;
 graph Target.construct;graph Raw.construct;graph Scope.construct;
 let measure construct=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(construct bytes(Lwt.return bytes)))done;Gc.allocated_bytes()-.start in
 let old=measure Target.construct and current=measure Raw.construct in require "exact constructor allocation"(old=current);
 Printf.printf "PASS: typed module packages preserve abstract signatures, physical packages/members/exceptions, generic members, state, promises/context/cancel, exact faults, natural Weak ownership and allocation %.0f B.\n%!"old
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_bindings.mli soma_bindings.ml prog.mli prog.ml raw.ml scope.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
cp package.definition original-definition
sed -i.bak 's/"Target.API"/"Target.Missing"/' package.definition
soma extract main.soma -no-soma-prelude -o missing >missing.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash
if (cd missing && dune build --profile release -j2)>missing-build.log 2>&1;then echo 'missing module signature accepted' >&2;exit 1;fi
if cmp -s before-abi missing/native_abi.manifest;then echo 'package type ABI unchanged' >&2;exit 1;fi
python3 - <<'PY'
from pathlib import Path
rows=lambda text:[line for line in text.splitlines()if len(line.split())>=3 and line.split()[2]=='main.main']
a=rows(Path('before-hash').read_text());b=rows(Path('changed-hash').read_text());assert a and b and a!=b
PY
