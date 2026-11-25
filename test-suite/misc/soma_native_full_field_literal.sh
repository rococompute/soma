#!/usr/bin/env bash
# Closed native field/literal calls retain original full-application boundaries.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 45 "$work"/*.log 2>/dev/null || true; fi; if [ "${KEEP:-0}" = 1 ]; then echo "Retained $work"; else rm -rf "$work"; fi; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
type 'a cell={mutable payload:'a;other:'a}
type 'a owner={mutable cell:'a cell}
let hook=ref(fun (_:string)->())
let take value extra= !hook "take";ignore extra;value
let trailing first literal= !hook literal;fun second-> !hook "second";ignore second;first
let leading literal first second= !hook literal;ignore second;first
let last first second literal= !hook literal;ignore second;first
let pending=ref(Lwt.return "")
let async value extra= !hook "async";ignore value;ignore extra;!pending
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner (A:Type) := "Target.owner".
OCaml Native External Value select : forall A:Type, owner A -> string -> A := "Target.take" Reading "cell" "Target.payload" AtFullApplication.
OCaml Native External Value one : forall A:Type, owner A -> A := "Fun.id" Reading "cell" "Target.payload" AtFullApplication.
OCaml Native External Value async : owner string -> string -> promise string := "Target.async" Reading "cell" "Target.payload" AtFullApplication.
OCaml Native External Value leading : string -> string -> string := "Target.leading" With "literal" After 0 AtFullApplication.
OCaml Native External Value middle : string -> string -> string := "Target.trailing" With "literal" After 1 AtFullApplication.
OCaml Native External Value last : string -> string -> string := "Target.last" With "literal" After 2 AtFullApplication.
Fail OCaml Native External Value no_function : string := "Target.take" Reading "cell" AtFullApplication.
Fail OCaml Native External Value scalar : string -> string := "Target.take" Reading "cell" AtFullApplication.
Fail OCaml Native External Value labelled : forall (receiver:owner string), string -> string := "Target.take" Reading "cell" AtFullApplication.
Fail OCaml Native External Value injected : owner string -> string := "Target.take" Reading "cell; assert false" AtFullApplication.
Fail OCaml Native External Value injected_target : owner string -> string := "Target.take; assert false" Reading "cell" AtFullApplication.
Fail OCaml Native External Value late_type : owner string -> forall A:Type, A -> A := "Target.take" Reading "cell" AtFullApplication.
Fail OCaml Native External Value too_far : string -> string := "Target.last" With "literal" After 2 AtFullApplication.
Fail OCaml Native External Value no_literal_function : string := "Target.last" With "literal" After 0 AtFullApplication.
Fail OCaml Native External Value literal_label : forall (input:string), string := "Target.last" With "literal" After 1 AtFullApplication.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
From Stdlib Require Import Strings.String.
Import target.
Definition public_select := Native.Export (Native.Call_callback (target.select string) tt).
Definition public_one := Native.Export (Native.Call_callback (target.one string) tt).
Definition public_async := Native.Export (Native.Call_callback target.async tt).
Definition public_leading := Native.Export (Native.Call_callback target.leading tt).
Definition public_middle := Native.Export (Native.Call_callback target.middle tt).
Definition public_last := Native.Export (Native.Call_callback target.last tt).
Definition main := (public_select,public_one,public_async,public_leading,public_middle,public_last).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let original_select record extra=Target.take record.Target.cell.Target.payload extra
let original_middle first second=Target.trailing first "literal" second
let collect()=Gc.full_major();Gc.full_major()
let cell payload={Target.payload;other="unread"}
let construct_original()=(fun first second->Target.trailing first "literal" second)
let construct_current()=(Soma_bindings.soma_native_746172676574_6d6964646c65())
let original_field()=(fun record extra->Target.take record.Target.cell.Target.payload extra)
let current_field()=Soma_bindings.soma_native_746172676574_73656c656374()
let original_one()=(fun record->Fun.id record.Target.cell.Target.payload)
let current_one()=Soma_bindings.soma_native_746172676574_6f6e65()
let ()=
 let old=String.make 1048576 'a' and fresh=String.make 1048576 'b' and extra=String.make 1048576 'c'in
 let owner={Target.cell=cell old}in
 let events=ref []in Target.hook:=(fun event->events:=event:: !events);
 let partial=Prog.public_select owner in require "partial has no target calls"(!events=[]);
 owner.cell<-cell fresh;
 require "fields reread only at full application"(partial extra==fresh&& !events=["take"]);
 require "unary live field"(Prog.public_one owner==fresh);
 let bytes=Bytes.create 1024 in let generic={Target.cell={Target.payload=bytes;other=bytes}}in
 require "parametric native field/result without conversion"(current_one()generic==bytes);
 let number=Sys.opaque_identity 1.25 in let generic_float={Target.cell={Target.payload=number;other=number}}in
 require "native float box borrowed"(current_one()generic_float==number);
 require "unary closed sharing"((original_one()==original_one())=(current_one()==current_one()));
 events:=[];
 let middle=Prog.public_middle old in require "literal partial is quiet"(!events=[]);
 require "middle returns borrowed payload"(middle extra==old&& !events=["second";"literal"]);
 events:=[];require "leading insertion"(Prog.public_leading old extra==old&& !events=["literal"]);
 events:=[];require "trailing insertion"(Prog.public_last old extra==old&& !events=["literal"]);
 require "literal function closed sharing"((construct_original()==construct_original())=(construct_current()==construct_current()));
 require "field function closed sharing"((original_field()==original_field())=(current_field()==current_field()));
 let fault=Failure "full native boundary"in Target.hook:=(fun _->raise fault);
 require "field synchronous exception identity"(try ignore(Prog.public_select owner extra);false with error->error==fault);
 require "literal synchronous exception identity"(try ignore(Prog.public_middle old extra);false with error->error==fault);
 let promise,_=Lwt.task()in Target.pending:=promise;let key=Lwt.new_key()in
 Target.hook:=(fun _->require "caller dynamic context"(Lwt.get key=Some "caller"));
 Lwt.with_value key(Some "caller")(fun()->require "borrowed native promise"(Prog.public_async owner extra==promise));
 Lwt.cancel promise;require "cancellation unchanged"(match Lwt.state promise with Lwt.Fail Lwt.Canceled->true|_->false);
 Target.hook:=(fun _->());
 let measure fn=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.before in
 let compare name a b=let before=measure a and after=measure b in require name(before=after);Printf.printf "%s %.0f/%.0f B\n%!"name before after in
 compare "literal closed creation"(fun()->construct_original())(fun()->construct_current());
 compare "field closed creation"(fun()->original_field())(fun()->current_field());
 compare "unary closed creation"(fun()->original_one())(fun()->current_one());
 compare "literal direct call"(fun()->original_middle old extra)(fun()->Prog.public_middle old extra);
 compare "field direct call"(fun()->original_select owner extra)(fun()->Prog.public_select owner extra);
 let check_weak select=
  let slot=Weak.create 1 and keep=ref None in
  let[@inline never] prepare()=let payload=String.make(16*1024*1024)'w'in Weak.set slot 0(Some payload);
   let owner={Target.cell=cell payload}in let partial=select owner in owner.cell<-cell "replacement";keep:=Some(owner,partial)in
  prepare();collect();require "partial retains owner, releases old field"(not(Weak.check slot 0));
  let owner,partial=Option.get !keep in require "partial observes replacement"(partial extra==owner.cell.payload);
  let owner_slot=Weak.create 1 in Weak.set owner_slot 0(Some owner);
  keep:=None;ignore(Sys.opaque_identity partial);owner_slot in
 ignore(check_weak original_select);ignore(check_weak Prog.public_select);
 let released select=let slot=Weak.create 1 in
  let[@inline never] invoke()=let owner={Target.cell=cell(String.make 1048576 'w')}in Weak.set slot 0(Some owner);ignore(Sys.opaque_identity(select owner extra))in
  invoke();collect();not(Weak.check slot 0)in
 require "caller owner released after full call"(released original_select&&released Prog.public_select);
 print_endline "PASS: closed native field/literal functions preserve full-application timing, live mutable chains, arbitrary native types, sharing, direct allocations, faults, promises/context/cancellation and Weak lifetimes."
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_bindings.ml prog.mli prog.ml check.ml
 ./"check-$compiler"
done
# Missing fields and mismatched host result types must fail actual native compilation.
cp target.definition original.definition
for mode in missing wrong;do
 cp original.definition target.definition
 if [ "$mode" = missing ];then
  sed -i.bak 's/"Target.payload"/"Target.missing"/g' target.definition
 else
  sed -i.bak 's/owner A -> string -> A/owner A -> string -> bool/' target.definition
 fi
 soma extract main.soma -no-soma-prelude -o "bad-$mode" >"bad-$mode-extract.log" 2>&1
 if (cd "bad-$mode" && dune build --profile release -j2)>"bad-$mode-build.log" 2>&1;then echo "incorrect native field $mode accepted" >&2;exit 1;fi
 grep -Eq 'Error:|Unbound record field' "bad-$mode-build.log"
done
cp original.definition target.definition
cp native/native_abi.manifest before-abi
cp hash.log before-hash
for mode in literal position field;do
 cp original.definition target.definition
 case "$mode" in
 literal) sed -i.bak 's/With "literal" After 1/With "changed" After 1/' target.definition;;
 position) sed -i.bak 's/With "literal" After 1/With "literal" After 2/' target.definition;;
 field) sed -i.bak 's/"Target.payload"/"Target.other"/g' target.definition;;
 esac
 soma extract main.soma -no-soma-prelude -o "changed-$mode" >"changed-$mode.log" 2>&1
 soma hash main.soma -no-soma-prelude >"changed-$mode-hash"
 if cmp -s native/native_abi.manifest "changed-$mode/native_abi.manifest";then echo "native $mode identity unchanged" >&2;exit 1;fi
 if cmp -s before-hash "changed-$mode-hash";then echo "semantic $mode identity unchanged" >&2;exit 1;fi
done
