#!/usr/bin/env bash
# Generic checked functions are applied outside the sealed module, in place.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 25 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
let weak=Weak.create 1
let prepares=ref 0
let calls=ref 0
let context:string Lwt.key=Lwt.new_key()
let failure=Failure "original application"
let broken=ref false
let inspect=ref(fun (_:bytes) (_:string)->())
let response=ref(Lwt.return(Bytes.create 0))
let unit=()
let wrong=true
let make()=
 incr prepares;let owner=Bytes.make 1048576 'o'in Weak.set weak 0(Some owner);
 fun text->incr calls;(!inspect)owner text;if !broken then raise failure;!response
let other text=Bytes.of_string text
ML
cat >prefix.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native External Value unit_value : unit := "Target.unit".
OCaml Native External Value make : unit -> string -> Native.entry(promise buffer) := "Target.make".
OCaml Native Static Initialize prepared : string -> Native.entry(promise buffer) := make With [unit_value].
OCaml Native Reexport Binding provider := prepared.
OCaml Native External Value provider_value : string -> Native.entry(promise buffer) := "provider".
OCaml Native External Value other_value : string -> Native.entry buffer := "Target.other".
OCaml Native External Callback dynamic : string -> Native.entry buffer := "Target.other".
OCaml Native External Value wrong : bool := "Target.wrong".
OCaml Native External Exception bad := "Bad".
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
From Stdlib Require Import Strings.String.
Import prefix.
Definition borrow{A:Type}(call:string->Native.entry A)text:=call text.
Definition unused:=true.
Definition main:=let _ := (provider,provider_value,other_value,dynamic,wrong,bad)in @borrow.
Fail OCaml Native Static Assembly main As "Checked" Applications [Apply "unused" := unused With []] With [].
Fail OCaml Native Static Assembly main As "Checked" Applications [Apply "wrong" := borrow With [wrong]] With [].
Fail OCaml Native Static Assembly main As "Checked" Applications [Apply "dynamic" := borrow With [dynamic]] With [].
Fail OCaml Native Static Assembly main As "Checked" Applications [Apply "generic" := borrow With []] With [].
Fail OCaml Native Static Assembly main As "Checked" Applications [Apply "excess" := borrow With [provider_value;other_value;other_value]] With [].
Fail OCaml Native Static Assembly main As "Checked" Applications [Apply "repeat" := borrow With [provider_value];Apply "repeat" := borrow With [other_value]] With [].
OCaml Native Static Assembly main As "Checked" Applications [Apply "first" := borrow With [provider_value];Apply "second" := borrow With [other_value]]
 With [Exception "Bad" := bad].
OCaml Native Lexical Scope main.
OCaml Native Lexical Environment main Prefix [Exception bad;Values provider] Modules [] Local [].
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import shlex,hashlib
row=shlex.split(Path('native/native_assemblies.manifest').read_text().splitlines()[1])
for path,expected in [(row[1],row[2]),('native/'+row[3],row[4]),('native/prog.ml',row[5]),('native/prog.mli',row[6]),('native/soma_bindings.ml',row[7])]:
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==expected,path
code=Path('native/'+row[3]).read_text()
assert 'Checked.borrow (provider), Checked.borrow (Target.other)'in code
Path('fresh.ml').write_text('module Make()=struct\n'+code+'\nend\n')
for line in Path('hash.log').read_text().splitlines():
 assumptions=set(line.split('  assumes ',1)[1].split(', '))if'  assumes 'in line else set()
 assert assumptions<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},assumptions
PY
# Changing only the checked input changes the ABI/layout, even with the same
# inferred result type; no arbitrary OCaml expression is accepted as input.
cp main.soma original.soma
python3 - <<'PYCHANGE'
from pathlib import Path
p=Path('main.soma');s=p.read_text().replace('Apply "second" := borrow With [other_value]','Apply "second" := borrow With [provider_value]');p.write_text(s)
PYCHANGE
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
python3 - <<'PYCHECK'
from pathlib import Path
import shlex
old=shlex.split(Path('native/native_assemblies.manifest').read_text().splitlines()[1])
new=shlex.split(Path('changed/native_assemblies.manifest').read_text().splitlines()[1])
assert old[8]!=new[8], 'application inputs absent from layout identity'
PYCHECK
cp original.soma main.soma
# Re-extraction without the declaration must remove the stale assembly.
python3 - <<'PYCLEAN'
from pathlib import Path
p=Path('main.soma');p.write_text(p.read_text().split('\nOCaml Native Static Assembly main As')[0])
PYCLEAN
# The split retains Fail commands; these are harmless independent checks.
soma extract main.soma -no-soma-prelude -o changed >cleanup.log 2>&1
test ! -e changed/main.assembly
test ! -e changed/native_assemblies.manifest
cp original.soma main.soma
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cat >old.ml <<'ML'
module Make()=struct
 exception Bad
 let provider=Target.make()
 let first,second=
  let module Checked:sig val borrow:(string->'a)->string->'a end=struct let borrow call text=call text end in
  Checked.borrow provider,Checked.borrow Target.other
end
ML
cat >check.ml <<'ML'
module Before=Old.Make()
module After=Fresh.Make()
module A(X:module type of Before)=struct end
module B(X:module type of After)=struct end
module AB=A(After)
module BA=B(Before)
let require name value=if not value then failwith name
let[@inline never] allocated f=Gc.full_major();let before=Gc.allocated_bytes()in
 for _=1 to 1000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.before
let first_window create=
 let kept=ref None in let[@inline never] start()=kept:=Some(create())in
 start();Gc.full_major();Gc.full_major();let live=Weak.check Target.weak 0 in
 (match !kept with Some f->ignore(f "owner")|None->assert false);
 kept:=None;Gc.full_major();Gc.full_major();live,Weak.check Target.weak 0
let second_window create=
 let kept=ref None in let[@inline never] start()=kept:=Some(create())in
 start();Gc.full_major();Gc.full_major();let live=Weak.check Target.weak 0 in
 (match !kept with Some f->ignore(f "value")|None->assert false);
 kept:=None;Gc.full_major();Gc.full_major();live,Weak.check Target.weak 0
let ()=
 require "single initialization and no provider calls"(!Target.prepares=2&& !Target.calls=0);
 let promise,wake=Lwt.task()in Target.response:=promise;
 Target.inspect:=(fun owner text->require "owner/context"(Bytes.length owner=1048576&&text="value"&&Lwt.get Target.context=Some"original"));
 require "original promise"(Lwt.with_value Target.context(Some"original")(fun()->After.first "value")==promise);
 let payload=Bytes.make 16 'p'in Lwt.wakeup wake payload;require "original result"(Lwt_main.run promise==payload);
 Target.broken:=true;require "original throw"(try ignore(Lwt.with_value Target.context(Some"original")(fun()->After.first "value"));false with e->e==Target.failure);
 Target.broken:=false;Target.inspect:=(fun _ _->());
 let promise,_=Lwt.task()in Target.response:=promise;let result=After.first "cancel"in Lwt.cancel result;
 require "original cancellation"(result==promise&&Lwt.state promise=Lwt.Fail Lwt.Canceled);
 Target.response:=Lwt.return payload;
 let a=allocated(fun()->Before.first "value")and b=allocated(fun()->After.first "value")in require "exact call allocation"(a=b);
 let old=first_window(fun()->let module M=Old.Make()in M.first)and fresh=first_window(fun()->let module M=Fresh.Make()in M.first)in
 require "natural provider owner"(old=fresh&&fst old&&not(snd old));
 let old=second_window(fun()->let module M=Old.Make()in M.second)and fresh=second_window(fun()->let module M=Fresh.Make()in M.second)in
 require "independent member owner release"(old=fresh&&not(fst old)&&not(snd old));
 Printf.printf "PASS: complete applications API, inferred independent types, original promise/context/fault/cancel, exact call allocation %.0f/%.0f B and natural separate member ownership.\n"a b
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt.unix -linkpkg -w -a uint63.ml soma_nat.ml soma_word64.ml soma_handles.ml soma_effect.ml float64.ml target.ml old.ml fresh.ml check.ml -o check >"$compiler.log" 2>&1
 ./check
done
printf 'PASS: applied generic functions, invalid shapes/dependencies/arities/results, provenance and assumptions.\n'
