#!/usr/bin/env bash
# Deferred field paths borrow the owner and read the current chain only on unit invocation.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 45 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
type cell={mutable text:string;other:string;mutable callback:unit->string;mutable pending:string Lwt.t}
type owner={mutable cell:cell}
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "Target.owner".
OCaml Native Get Deferred text : owner -> unit -> string := "cell" "Target.text".
OCaml Native Get Deferred callback : owner -> unit -> (unit -> string) := "cell" "Target.callback".
OCaml Native Get Deferred pending : owner -> unit -> promise string := "cell" "Target.pending".
Fail OCaml Native Get Deferred scalar : string -> unit -> string := "length".
Fail OCaml Native Get Deferred wrong_trigger : owner -> string -> string := "cell" "Target.text".
Fail OCaml Native Get Deferred labelled : forall (value : owner), unit -> string := "cell" "Target.text".
Fail OCaml Native Get Deferred injected : owner -> unit -> string := "cell; failwith".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target.
Definition body := Native.Export (
 Native.Bind (Native.Call_callback text tt) (fun text =>
 Native.Bind (Native.Call_callback callback tt) (fun callback =>
 Native.Bind (Native.Call_callback pending tt) (fun pending =>
 Native.Return (text,(callback,pending)))))).
Definition main := body.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PYASSUMPTIONS'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes ' in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PYASSUMPTIONS
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/{prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml,target.ml} .
cat > check.ml <<'ML'
let require name condition=if not condition then failwith name
let make text={Target.text;other="other";callback=(fun()->text);pending=Lwt.return text}
let text,(callback,pending)=Prog.body
let context:string Lwt.key=Lwt.new_key()
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let first=String.make 1000000 'f'and second=String.make 1000000 's'in
 let owner={Target.cell=make first}in
 let thunk=text owner in require "borrowed initial field"(thunk()==first);
 let next=make second in owner.cell<-next;
 require "reads live field chain"(thunk()==second);
 let third=String.make 1000000 't'in next.text<-third;
 require "reads live terminal field"(thunk()==third);
 let calls=ref 0 and fault=Failure "deferred callback"in
 let exact()=incr calls;require "callback invocation scope"(Lwt.get context=Some "caller");raise fault in
 next.callback<-exact;let deferred=callback owner in
 require "construction and read do not invoke callback"(!calls=0&&deferred()==exact&& !calls=0);
 require "callback exact synchronous fault"(try Lwt.with_value context(Some "caller")(fun()->ignore((deferred())()));false with error->error==fault);
 let wait,wake=Lwt.task()and canceled=ref 0 in Lwt.on_cancel wait(fun()->incr canceled);next.pending<-wait;
 let deferred=pending owner in require "exact pending field"(deferred()==wait);Lwt.cancel(deferred());require "direct cancellation"(!canceled=1);ignore(Sys.opaque_identity wake);
 let rejected=Lwt.fail fault in next.pending<-rejected;require "exact rejected field"(deferred()==rejected);
 next.pending<-Lwt.return third;require "live ready field"(deferred()==next.pending);
 let measure prepare=collect();let before=Gc.allocated_bytes()in
  for _=1 to 10000 do ignore(Sys.opaque_identity(prepare()))done;Gc.allocated_bytes()-.before in
 let old=measure(fun()->fun()->owner.Target.cell.Target.text)
 and current=measure(fun()->text owner)in
 Printf.printf "deferred field construction allocation %.0f/%.0f B\n%!"old current;
 require "original one-owner closure allocation"(old=current);
 let old_thunk()=owner.Target.cell.Target.text in
 let old=measure(fun()->old_thunk())and current=measure(fun()->thunk())in require "getter has no execution bridge"(old=current);
 let owner_weak=Weak.create 1 and old_cell_weak=Weak.create 1 in
 let[@inline never] prepare()=
  let cell=make(String.make 1048576 'b')in let owner={Target.cell}in
  Weak.set owner_weak 0(Some owner);Weak.set old_cell_weak 0(Some cell);text owner in
 let held=ref(Some(prepare()))in collect();require "thunk retains owner and its current fields"(Weak.check owner_weak 0&&Weak.check old_cell_weak 0);
 ignore(Sys.opaque_identity((Option.get !held)()));
 let[@inline never] replace()=let owner=Option.get(Weak.get owner_weak 0)in owner.Target.cell<-make "replacement"in
 replace();collect();require "thunk does not retain consumed old field"(Weak.check owner_weak 0&&not(Weak.check old_cell_weak 0));
 require "retained thunk reads replacement"((Option.get !held)()="replacement");
 held:=None;collect();require "dropping thunk releases owner"(not(Weak.check owner_weak 0));
 print_endline "PASS: checked deferred field getters preserve live reads, borrowed values/callbacks/promises, faults, caller context, cancellation, owner Weak phases and exact closure allocations."
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_bindings.ml prog.mli prog.ml check.ml
 "./check-$compiler"
done
# Field-chain and result mismatches must be rejected by the typed native boundary.
# Retain the same foreign module, so its real native implementation is compiled.
cp target.definition original-target.definition
sed 's/"Target.text"/"Target.missing"/' original-target.definition > target.definition
soma extract main.soma -no-soma-prelude -o bad-native >bad-extract.log 2>&1
if (cd bad-native && dune build --profile release -j2)>bad-build.log 2>&1;then echo 'accepted missing native field' >&2;exit 1;fi
rg -q 'Unbound record field (Target\.)?missing' bad-build.log
sed 's/owner -> unit -> string :=/owner -> unit -> bool :=/' original-target.definition > target.definition
soma extract main.soma -no-soma-prelude -o mismatch-native >mismatch-extract.log 2>&1
if (cd mismatch-native && dune build --profile release -j2)>mismatch-build.log 2>&1;then echo 'accepted wrong native result type' >&2;exit 1;fi
rg -q 'type bool' mismatch-build.log
cp original-target.definition target.definition
# Same-typed field paths in the same project invalidate semantic and native ABI receipts.
cp native/native_abi.manifest baseline-abi
cp hash.log baseline-hashes
sed -i.bak 's/"Target.text"/"Target.other"/' target.definition
soma extract main.soma -no-soma-prelude -o changed-native >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hashes
if cmp -s baseline-abi changed-native/native_abi.manifest;then echo 'field path absent from native ABI' >&2;exit 1;fi
python3 - <<'PYHASH'
from pathlib import Path
def hashes(path):
 return {line.split()[2]:line.split()[:2] for line in Path(path).read_text().splitlines() if len(line.split())>=3}
a=hashes('baseline-hashes');b=hashes('changed-hashes')
for key in ('main.body','main.main','target.text'):
 assert a[key][0]!=b[key][0] and a[key][1]!=b[key][1],(key,a[key],b[key])
PYHASH
