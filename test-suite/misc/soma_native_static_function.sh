#!/usr/bin/env bash
# Static composition/prefix binding keep closed wrappers and native arity.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 50 "$work"/*.log 2>/dev/null || true; fi; if [ "${KEEP:-0}" = 1 ]; then echo "Retained $work"; else rm -rf "$work"; fi; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
type owner={mutable payload:string}
type config={mutable prefix:string}
let config={prefix="original"}
let tag=7
let dynamic()=config
let hook=ref(fun (_:string)(_ :string)->())
let get owner literal= !hook "get" literal;owner.payload
let outer value= !hook "outer" value;fun missing path-> !hook "last" path;ignore missing;value
let relative config ~base path= !hook "relative" config.prefix;ignore path;base
let none:string option=None
let optional ?(prefix="default") value= !hook "optional" prefix;value
let adjust config ?(mode=3) value= !hook config.prefix(string_of_int mode);value
let join first second= !hook "join" second;first
let keep value extra=ignore extra;value
let tagged tag value=ignore tag;value
let pending=ref(Lwt.return "")
let async value missing path= !hook "async" value;ignore missing;ignore path;!pending
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "Target.owner".
OCaml Native External Type config := "Target.config".
OCaml Native External Value get : owner -> string := "Target.get" With "/" After 1 AtFullApplication.
OCaml Native External Value outer : string -> PrimInt63.int -> string -> string := "Target.outer".
OCaml Native External Value async : string -> PrimInt63.int -> string -> promise string := "Target.async".
OCaml Native Callable canonical_call := owner -> forall(missing:PrimInt63.int), string -> string.
OCaml Native Callable async_call := owner -> forall(missing:PrimInt63.int), string -> promise string.
OCaml Native Static Compose canonical : canonical_call := outer With get.
OCaml Native Static Compose suspended : async_call := async With get.
OCaml Native External Value config_value : config := "Target.config".
OCaml Native Callable relative_target := config -> forall(base:string), string -> string.
OCaml Native External Value relative : relative_target := "Target.relative".
OCaml Native Callable relative_call := forall(base:string), string -> string.
OCaml Native Static Prefix prefix : relative_call := relative With config_value.
OCaml Native External Value uppercase : string -> string := "String.uppercase_ascii".
OCaml Native Static Compose nested : string -> string -> string := prefix With uppercase.
OCaml Native External Value none_value : option string := "Target.none".
OCaml Native Callable optional_target Optional prefix := forall(prefix:option string), string -> string.
OCaml Native External Value optional : optional_target := "Target.optional".
OCaml Native Static Prefix default_optional : string -> string := optional With none_value.
OCaml Native Callable adjust_target Optional mode := config -> forall(mode:option PrimInt63.int), string -> string.
OCaml Native External Value adjust : adjust_target := "Target.adjust".
OCaml Native Callable adjusted_call Optional mode := forall(mode:option PrimInt63.int), string -> string.
OCaml Native Static Prefix adjusted : adjusted_call := adjust With config_value.
OCaml Native External Value join : string -> string -> string := "Target.join".
OCaml Native Static Compose multi : string -> string -> PrimInt63.int -> string -> string := outer With join.
OCaml Native External Value generic_outer : forall A:Type, A -> string -> A := "Target.keep".
OCaml Native External Value identity : forall A:Type, A -> A := "Fun.id".
OCaml Native Static Compose generic : forall A:Type, A -> string -> A := generic_outer With identity.
OCaml Native External Value tag : PrimInt63.int := "Target.tag".
OCaml Native External Value tagged : forall A:Type, PrimInt63.int -> A -> A := "Target.tagged".
OCaml Native Static Prefix generic_prefix : forall A:Type, A -> A := tagged With tag.
OCaml Native External Callback dynamic : unit -> config := "Target.dynamic".
OCaml Native External Value allocating : string := "Fun.id" With "creation".
OCaml Native External Value uses_string : string -> string -> string := "Target.keep".
Fail OCaml Native Static Compose not_function : string := outer With get.
Fail OCaml Native Static Compose wrong_argument : string -> PrimInt63.int -> string -> string := outer With get.
Fail OCaml Native Static Compose wrong_result : owner -> PrimInt63.int -> string -> bool := outer With get.
Fail OCaml Native Static Compose wrong_inner : owner -> string := outer With config_value.
Fail OCaml Native Static Prefix wrong_value : string -> string := relative With tag.
Fail OCaml Native Static Prefix unsafe_getter : relative_call := relative With dynamic.
Fail OCaml Native Static Prefix creation_call : string -> string := uses_string With allocating.
Fail OCaml Native Static Compose missing_type : string -> string := generic_outer With identity.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
From Stdlib Require Import Strings.String.
Import target.
Definition canonical_fn := Native.Export(Native.Call_callback canonical tt).
Definition suspended_fn := Native.Export(Native.Call_callback suspended tt).
Definition prefix_fn := Native.Export(Native.Call_callback prefix tt).
Definition nested_fn := Native.Export(Native.Call_callback nested tt).
Definition generic_fn := Native.Export(Native.Call_callback(generic string)tt).
Definition generic_prefix_fn := Native.Export(Native.Call_callback(generic_prefix string)tt).
Definition optional_fn := Native.Export(Native.Call_callback default_optional tt).
Definition adjusted_fn := Native.Export(Native.Call_callback adjusted tt).
Definition multi_fn := Native.Export(Native.Call_callback multi tt).
Definition main := (canonical_fn,suspended_fn,prefix_fn,nested_fn,generic_fn,generic_prefix_fn,optional_fn,adjusted_fn,multi_fn).
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
cp native/soma_callable_*.ml .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let original_canonical()=(fun owner ~missing path->Target.outer(Target.get owner "/")missing path)
let current_canonical()=Soma_bindings.soma_native_746172676574_63616e6f6e6963616c()
let original_prefix()=(fun ~base path->Target.relative Target.config ~base path)
let current_prefix()=Soma_bindings.soma_native_746172676574_707265666978()
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let payload=String.make(16*1024*1024)'p'and path=String.make 1048576 'x'in
 let owner={Target.payload}in
 let events=ref []in Target.hook:=(fun event value->events:=(event,value):: !events);
 let f=Prog.canonical_fn owner in require "partial outer/inner calls are quiet"(!events=[]);
 let f=f ~missing:13 in require "required label partial is quiet"(!events=[]);
 let fresh=String.make 1048576 'f'in owner.payload<-fresh;
 require "borrowed live inner result"(f path==fresh);
 require "full construction/call order"(List.map fst(List.rev !events)=["get";"outer";"last"]);
 require "canonical closed native/bytecode sharing"((original_canonical()==original_canonical())=(current_canonical()==current_canonical()));
 require "prefix closed native/bytecode sharing"((original_prefix()==original_prefix())=(current_prefix()==current_prefix()));
 events:=[];let p=Prog.prefix_fn ~base:fresh in require "prefix partial quiet"(!events=[]);
 Target.config.prefix<-"changed";require "prefix borrowed result"(p path==fresh);
 require "live bound dictionary"(!events=["relative","changed"]);
 require "nested static composition"(Prog.nested_fn "abc" path="ABC");
 events:=[];require "optional input default"(Prog.optional_fn fresh==fresh&& !events=["optional","default"]);
 events:=[];require "optional output default"(Prog.adjusted_fn fresh==fresh&& !events=["changed","3"]);
 events:=[];require "optional output override"(Prog.adjusted_fn ~mode:17 fresh==fresh&& !events=["changed","17"]);
 events:=[];let multi=Prog.multi_fn fresh path in require "multi-argument inner waits for full application"(!events=[]);
 require "multi-argument inner result"(multi 13 path==fresh&&List.map fst(List.rev !events)=["join";"outer";"last"]);
 require "generic composition"(Prog.generic_fn fresh path==fresh&&Prog.generic_prefix_fn fresh==fresh);
 let bytes=Bytes.create 1024 in
 require "polymorphic native result unchanged"(Soma_bindings.soma_native_746172676574_67656e65726963()bytes path==bytes);
 let callback()=payload in
 require "polymorphic returned callback unchanged"(Soma_bindings.soma_native_746172676574_67656e65726963()callback path==callback);
 let fault=Failure "exact native fault"in Target.hook:=(fun _ _->raise fault);
 require "direct fault identity"(try ignore(Prog.canonical_fn owner ~missing:0 path);false with error->error==fault);
 let promise,_=Lwt.task()in Target.pending:=promise;let key=Lwt.new_key()in
 Target.hook:=(fun _ _->require "dynamic Lwt context"(Lwt.get key=Some "caller"));
 Lwt.with_value key(Some "caller")(fun()->require "original pending promise"(Prog.suspended_fn owner ~missing:0 path==promise));
 Lwt.cancel promise;require "native cancellation"(match Lwt.state promise with Lwt.Fail Lwt.Canceled->true|_->false);
 Target.hook:=(fun _ _->());
 let measure fn=collect();let start=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.start in
 let compare name old current=let a=measure old and b=measure current in require name(a=b);Printf.printf "%s %.0f/%.0f B\n%!"name a b in
 compare "canonical creation"original_canonical current_canonical;
 compare "prefix creation"original_prefix current_prefix;
 let old=original_canonical()and current=current_canonical()in
 compare "canonical invocation"(fun()->old owner ~missing:13 path)(fun()->current owner ~missing:13 path);
 let old=original_prefix()and current=current_prefix()in
 compare "prefix invocation"(fun()->old ~base:fresh path)(fun()->current ~base:fresh path);
 let released fn=let weak=Weak.create 1 in
  let[@inline never] call()=let owner={Target.payload=String.make 1048576 'w'}in Weak.set weak 0(Some owner);ignore(Sys.opaque_identity(fn owner ~missing:0 path))in
  call();collect();not(Weak.check weak 0)in
 require "owners released after full calls"(released(original_canonical())&&released(current_canonical()));
 let retained fn=let owner_slot=Weak.create 1 and old_slot=Weak.create 1 in
  let[@inline never] prepare()=let old=String.make 1048576 'o'in let owner={Target.payload=old}in
   Weak.set owner_slot 0(Some owner);Weak.set old_slot 0(Some old);let partial=fn owner in owner.payload<-fresh;partial in
  let partial=prepare()in collect();require "partial owns caller but not stale field"(Weak.check owner_slot 0&&not(Weak.check old_slot 0));
  require "partial returns fresh field"(partial ~missing:0 path==fresh)in
 retained(original_canonical());retained(current_canonical());
 print_endline "PASS: static native functions retain labels, full-call timing, closed sharing, exact allocation, generic identities, faults, promises/context/cancellation and Weak lifetimes."
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_callable_*.ml soma_bindings.ml prog.mli prog.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
soma hash main.soma -no-soma-prelude >before-hash
sed -i.bak 's/With "\/" After 1/With "changed" After 1/' target.definition
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash
if cmp -s before-abi changed/native_abi.manifest;then echo 'nested static ABI failed to change' >&2;exit 1;fi
python3 - <<'PY'
from pathlib import Path
def read(file):return {x.split()[2]:x.split()[:2]for x in Path(file).read_text().splitlines()if len(x.split())>=3}
a=read('before-hash');b=read('changed-hash')
for name in ('target.canonical','target.suspended','main.canonical_fn','main.suspended_fn'):
 assert a[name][0]!=b[name][0]and a[name][1]!=b[name][1],(name,a[name],b[name])
PY
