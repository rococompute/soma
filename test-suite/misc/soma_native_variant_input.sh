#!/usr/bin/env bash
# Checked publication widens closed row inputs without changing runtime values.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 24 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type owner={bytes:bytes}
type mode=[`U|`L of owner|`N of string]
let calls=ref 0
let context:string Lwt.key=Lwt.new_key()
let observe=ref(fun (_:mode) (_:bytes)->())
let failure=Failure "original variant fault"
let broken=ref false
let response=ref(Lwt.return(Bytes.create 0))
let call (mode:mode) (bytes:bytes)=incr calls;(!observe)mode bytes;if !broken then raise failure;!response
let dual a (_:mode) bytes=call a bytes
ML
cat >row.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "Target.owner".
OCaml Native Polymorphic Variant mode := ["U";"L":owner;"N":string].
OCaml Native External Value target : mode -> buffer -> promise buffer := "Target.call".
OCaml Native External Value pair_target : mode -> mode -> buffer -> promise buffer := "Target.dual".
OCaml Native External Callback dynamic : mode -> buffer -> promise buffer := "Target.call".
Fail OCaml Native Reexport Variant Input wrong := target At 1 Parameters ["mode";"bytes"].
Fail OCaml Native Reexport Variant Input outside := target At 2 Parameters ["mode";"bytes"].
Fail OCaml Native Reexport Variant Input short := target At 0 Parameters ["mode"].
Fail OCaml Native Reexport Variant Input repeated := target At 0 Parameters ["mode";"mode"].
Fail OCaml Native Reexport Variant Input wildcard := target At 0 Parameters ["_";"bytes"].
Fail OCaml Native Reexport Variant Input injected := target At 0 Parameters ["x);failwith";"bytes"].
Fail OCaml Native Reexport Variant Input runtime := dynamic At 0 Parameters ["mode";"bytes"].
OCaml Native Open Polymorphic Variant open_mode(Row:Type) := ["U"].
OCaml Native External Value open_target : forall Row:Type,open_mode Row->buffer->promise buffer := "Target.call".
Fail OCaml Native Reexport Variant Input open_domain := open_target At 0 Parameters ["mode";"bytes"].
OCaml Native Callable labelled_call := forall(mode:mode),buffer->promise buffer.
OCaml Native External Value labelled : labelled_call := "Target.call".
Fail OCaml Native Reexport Variant Input labelled_domain := labelled At 0 Parameters ["mode";"bytes"].
OCaml Native Reexport Variant Input adapt := target At 0 Parameters ["mode";"bytes"].
OCaml Native Reexport Variant Input dual := pair_target At 0 Parameters ["first";"second";"bytes"].
SOMA
cat >main.soma <<'SOMA'
Import row.
Definition main:=(adapt,dual).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import shlex,hashlib
rows=[shlex.split(r)for r in Path('native/native_value_reexports.manifest').read_text().splitlines()[1:]]
assert [r[6]for r in rows]==['adapt','dual'] and len({r[4]for r in rows})==1
for _,_,source,src_hash,name,digest,*_ in rows:
 assert hashlib.sha256(Path(source).read_bytes()).hexdigest()==src_hash
 assert hashlib.sha256(Path('native',name).read_bytes()).hexdigest()==digest
Path('fresh.ml').write_bytes(Path('native',rows[0][4]).read_bytes())
assert '[<'in Path('fresh.ml').read_text() and ':>'in Path('fresh.ml').read_text()
assert 'native-variant-input-v1'in Path('native/native_abi.manifest').read_text()
assert all('  assumes 'not in l for l in Path('hash.log').read_text().splitlines())
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cp native/soma_variant_*.ml .
cat >old.ml <<'ML'
let adapt(mode:[<`U|`L of Target.owner|`N of string]) bytes=Target.call(mode:>Target.mode)bytes
let dual(first:[<`U|`L of Target.owner|`N of string]) second bytes=Target.dual(first:>Target.mode)second bytes
ML
cat >check.ml <<'ML'
module A(X:module type of Old)=struct end
module B(X:module type of Fresh)=struct end
module AB=A(Fresh)
module BA=B(Old)
let require name value=if not value then failwith name
let[@inline never] allocated fn=Gc.full_major();let before=Gc.allocated_bytes()in
 for _=1 to 1000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.before
let narrow(f:[`U]->bytes->bytes Lwt.t)=f `U
let window adapt=
 let weak=Weak.create 1 and kept=ref None in
 let[@inline never] create()=let owner={Target.bytes=Bytes.make 1048576 'x'}in
 Weak.set weak 0(Some owner);kept:=Some(adapt(`L owner))in
 create();Gc.full_major();Gc.full_major();let live=Weak.check weak 0 in
 let[@inline never] use()=match !kept with Some f->ignore(f(Bytes.create 0))|None->assert false in
 use();kept:=None;Gc.full_major();Gc.full_major();live,Weak.check weak 0
let ()=
 require "no initialization call"(!Target.calls=0);
 let bytes=Bytes.make 64 'b'and owner={Target.bytes=Bytes.make 16 'o'}in
 let mode=`L owner in
 let response,wake=Lwt.task()in Target.response:=response;
 Target.observe:=(fun actual received->require "original row/payload bytes"(actual==mode&&received==bytes);require "caller context"(Lwt.get Target.context=Some"caller"));
 require "original pending promise"(Lwt.with_value Target.context(Some"caller")(fun()->Fresh.adapt mode bytes)==response);
 Lwt.wakeup wake bytes;require "original result"(Lwt_main.run response==bytes);
 Target.broken:=true;
 require "original synchronous fault"(try ignore(Lwt.with_value Target.context(Some"caller")(fun()->Fresh.adapt mode bytes));false with e->e==Target.failure);
 Target.broken:=false;Target.observe:=(fun _ _->());
 let promise,_=Lwt.task()in Target.response:=promise;let result=narrow Fresh.adapt bytes in
 Lwt.cancel result;require "original cancellation"(result==promise&&Lwt.state promise=Lwt.Fail Lwt.Canceled);
 Target.response:=Lwt.return bytes;
 let before=allocated(fun()->Old.adapt mode bytes)and after=allocated(fun()->Fresh.adapt mode bytes)in
 require "exact call allocation"(before=after);
 let a=window Old.adapt and b=window Fresh.adapt in require "natural original variant owner"(a=b&&fst a&&not(snd a));
 Printf.printf "PASS: complete upper-row API/subtypes, original row/payload/promise/context/fault/cancel, exact allocation %.0f/%.0f B and natural Weak lifetime.\n"before after
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt.unix -linkpkg -w -a uint63.ml soma_nat.ml soma_word64.ml soma_handles.ml soma_effect.ml float64.ml target.ml soma_variant_*.ml old.ml fresh.ml check.ml -o check >"$compiler.log" 2>&1
 ./check
done
cp hash.log before.log
sed -i.bak 's/dual := pair_target At 0/dual := pair_target At 1/' row.definition
soma hash main.soma -no-soma-prelude >after.log
python3 - <<'PY'
from pathlib import Path
def value(file,symbol):return next(l.split()[0]for l in Path(file).read_text().splitlines()if l.split()[2]==symbol)
assert value('before.log','row.dual')!=value('after.log','row.dual')
assert value('before.log','main.main')!=value('after.log','main.main')
assert value('before.log','row.adapt')==value('after.log','row.adapt')
PY
printf 'Definition main:=true.\n' >main.soma
soma extract main.soma -no-soma-prelude -o native >plain.log 2>&1
test ! -e native/native_value_reexports.manifest
printf 'PASS: closed-domain validation, metadata/ABI/provenance/assumptions, hash sensitivity and stale publication cleanup.\n'
