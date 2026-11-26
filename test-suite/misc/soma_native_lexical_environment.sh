#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 30 "$work"/*.log 2>/dev/null||true;fi;if [ "${KEEP:-0}" = 1 ];then echo "Retained $work";else rm -rf "$work";fi;exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type owner={mutable run:bytes->bytes Lwt.t}
type other={run:bytes->bytes Lwt.t}
let context:int Lwt.key=Lwt.new_key()
let seen=ref None
let response,wake=Lwt.task()
let fault=ref None
let original bytes=seen:=Lwt.get context;ignore(Sys.opaque_identity bytes);match !fault with Some error->raise error|None->response
let owner:owner={run=original}
let bytes=Bytes.make 4096 'b'
let trace=ref []
let failure=Failure "lexical environment"
let fail_setup=ref false
let weak=Weak.create 1
module type API=sig type t val id:t end
module Network(S:API)=struct
 exception Token
 let ()=trace:="network":: !trace
 let observe value=assert(value==S.id);trace:="observe":: !trace
end
module Setup(B:API)=struct
 let ()=trace:="setup":: !trace;if !fail_setup then raise failure
 let token=Bytes.make 1048576 'w'
 let ()=Weak.set weak 0(Some token)
 let forward value run bytes=ignore(Sys.opaque_identity token);assert(value==B.id);run bytes
end
module S=struct type t=bytes let id=Bytes.make 8192 's' end
module B=struct type t=bytes let id=Bytes.make 8192 'b' end
ML
cat >prefix.definition <<'SOMA'
From Soma Require Import Native Handles.
OCaml Native External Type owner_type := "Target.owner".
OCaml Native External Value owner_value : owner_type := "Target.owner".
OCaml Native Reexport Binding owner := owner_value.
OCaml Native Get run_selector : owner_type->buffer->promise buffer := "run".
OCaml Native Static Project read_run : buffer->promise buffer := run_selector From owner.
OCaml Native Reexport Binding run := read_run.
OCaml Native External Value bytes_value : buffer := "Target.bytes".
OCaml Native Static Initialize initial_promise : promise buffer := read_run With [bytes_value].
OCaml Native Reexport Binding prepared := initial_promise.
OCaml Native External Type other := "Target.other".
OCaml Native Get wrong_selector : other->buffer->promise buffer := "run".
Fail OCaml Native Static Project wrong : buffer->promise buffer := wrong_selector From owner.
Fail OCaml Native Static Project wrong : bool := run_selector From owner.
Fail OCaml Native Static Project wrong : buffer->promise buffer := owner_value From owner.
Fail OCaml Native Static Project wrong : buffer->promise buffer := run_selector From owner_value.
Module Modules.
OCaml Native Module Alias Network := "Target.Network".
End Modules.
SOMA
cat >calls.definition <<'SOMA'
From Soma Require Import Native Handles.
OCaml Native External Type stack := "S.t".
OCaml Native External Type block := "B.t".
OCaml Native External Value observe : stack->unit := "N.observe".
OCaml Native External Value forward : block->(buffer->promise buffer)->buffer->promise buffer := "Setup.forward".
OCaml Native External Value raw_run : buffer->promise buffer := "run".
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native Handles OCaml.
Import prefix calls.
Definition start stack block bytes := Native.Export(
 Native.Bind(Native.Call_callback observe tt)(fun observe=>
 Native.Bind(Native.Call_callback forward tt)(fun forward=>
 Native.Bind(Native.Call_callback raw_run tt)(fun run=>
 Native.Invoke(fun _=>observe stack)(fun _=>Native.tail_invoke(fun _=>forward block run bytes)))))).
Definition main := let _ := (prefix.run,prefix.Modules.Network)in start.
OCaml Native Static Assembly main As "Checked" With [Value "start" := start].
OCaml Native Lexical Scope main Open ["Target"] Functor "Main" With ["S":"Target.API";"B":"Target.API"].
Fail OCaml Native Lexical Environment main Prefix [Modules prefix.run] Modules [] Local [].
Fail OCaml Native Lexical Environment main Prefix [Values prefix.run;Values prefix.owner] Modules [] Local [].
Fail OCaml Native Lexical Environment main Prefix [] Modules [Module "S" := "Target.S"] Local [].
Fail OCaml Native Lexical Environment main Prefix [] Modules [] Local [Module "Checked" := "Target.B"].
Fail OCaml Native Lexical Environment main Prefix [] Modules [Module "N" := "Target.Network" Apply ["S;code"]] Local [].
Fail OCaml Native Lexical Environment main Prefix [] Modules [Module "n" := "Target.Network" Apply ["S"]] Local [].
Fail OCaml Native Lexical Environment main Prefix [] Modules [Module "N" := "Target.Network" Apply ["S"]] Local [Module "N" := "Target.B"].
OCaml Native Lexical Environment main Prefix [Values prefix.run;Modules prefix.Modules.Network]
 Modules [Module "N" := "Network" Apply ["S"]] Local [Module "Setup" := "Target.Setup" Apply ["B"]].
Fail OCaml Native Lexical Environment main Prefix [] Modules [] Local [].
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import shlex,hashlib
row=shlex.split(Path('native/native_assemblies.manifest').read_text().splitlines()[1]);assert len(row)==10
_,source,digest,file,product,program,interface,bindings,layout,contract=row
for path,expected in[(source,digest),('native/'+file,product),('native/prog.ml',program),('native/prog.mli',interface),('native/soma_bindings.ml',bindings)]:assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==expected
assert all('  assumes 'not in line or line.split('  assumes ',1)[1]=='Corelib.Numbers.Cyclic.Int63.PrimInt63.int'for line in Path('hash.log').read_text().splitlines())
Path('after.ml').write_bytes(Path('native/main.assembly').read_bytes())
assert 'Soma_published_'not in Path('native/soma_bindings.ml').read_text()
Path('before.ml').write_text('''open Target
let owner=Target.owner
let run=owner.run
let prepared=owner.run Target.bytes
module Network=Target.Network
module Main(S:Target.API)(B:Target.API)=struct
 module N=Network(S)
 let start=let module Setup=Target.Setup(B)in
 let module Checked:sig\n'''+Path('native/prog.mli').read_text()+'''\nend=struct
 module Soma_bindings=struct\n'''+Path('native/soma_bindings.ml').read_text()+'''\nend\n'''+Path('native/prog.ml').read_text()+'''\nend in Checked.start
end
''')
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cat >check.ml <<'ML'
let require label ok=if not ok then failwith label
let collect()=Gc.full_major();Gc.full_major()
module A(X:module type of Before)=struct end
module B(X:module type of After)=struct end
module AB=A(After)
module BA=B(Before)
let ()=
 require "single shared owner and callback snapshot"(Before.owner==After.owner&&Before.run==After.run&&After.run==Target.original&&Before.prepared==After.prepared&&After.prepared==Target.response);
 Target.trace:=[];let module Old=Before.Main(Target.S)(Target.B)in let old_trace=List.rev !Target.trace in
 Target.trace:=[];let module Fresh=After.Main(Target.S)(Target.B)in require "functor/module initialization order"(old_trace=["network";"setup"]&&List.rev !Target.trace=old_trace);
 require "separate generative exception slots"(Old.N.Token!=Fresh.N.Token);
 let bytes=Bytes.make 1048576 'p'in
 Target.trace:=[];
 Lwt.with_value Target.context(Some 42)(fun()->require "original caller/promise/payload"(Fresh.start Target.S.id Target.B.id bytes==Target.response&& !Target.seen=Some 42));
 require "network before provider"(!Target.trace=["observe"]);
 let failure=Failure "original"in Target.fault:=Some failure;
 require "original synchronous fault"(try ignore(Fresh.start Target.S.id Target.B.id bytes);false with e->e==failure);Target.fault:=None;
 let measure f=collect();let start=Gc.allocated_bytes()in for _=1 to 1000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.start in
 let a=measure(fun()->Old.start Target.S.id Target.B.id bytes)and b=measure(fun()->Fresh.start Target.S.id Target.B.id bytes)in require "exact call allocation"(a=b);
 Target.owner.run<-(fun _->failwith "new field");require "original snapshot after mutation"(After.run bytes==Target.response);
 Target.fail_setup:=true;Target.trace:=[];
 require "local module original init fault"(try let module Bad=After.Main(Target.S)(Target.B)in ignore Bad.start;false with error->error==Target.failure);
 require "fault phase"(List.rev !Target.trace=["network";"setup"]);
 Target.fail_setup:=false;
 let held=ref None in
 let[@inline never] install_before()=let module Scoped=Before.Main(Target.S)(Target.B)in held:=Some Scoped.start in
 let[@inline never] install_after()=let module Scoped=After.Main(Target.S)(Target.B)in held:=Some Scoped.start in
 List.iter(fun install->install();collect();require "live local functor payload"(Weak.check Target.weak 0);held:=None;collect();require "natural local functor release"(not(Weak.check Target.weak 0)))[install_before;install_after];
 Lwt.cancel Target.response;require "original promise cancellation"(match Lwt.state Target.response with Lwt.Fail Lwt.Canceled->true|_->false);
 Printf.printf "PASS: complete scoped API, direct published field snapshots, functor order/generative slots, original promise/context/fault/cancel and exact allocation %.0f/%.0f B.\n"a b
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml before.ml after.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
python3 - <<'PY2'
from pathlib import Path
p=Path('main.soma');p.write_text(p.read_text().replace(':= "Network" Apply',':= "Target.Network" Apply'))
PY2
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
if cmp -s hash.log changed-hash.log||cmp -s before-abi changed/native_abi.manifest;then echo 'lexical environment omitted from fingerprints' >&2;exit 1;fi
python3 - <<'PY2'
from pathlib import Path
p=Path('main.soma');p.write_text(p.read_text().replace(':= "Target.Network" Apply',':= "Network" Apply'))
p=Path('prefix.definition');p.write_text(p.read_text().replace('Binding prepared :=','Binding warmed :='))
PY2
soma hash main.soma -no-soma-prelude >prefix-hash.log
python3 - <<'PY2'
from pathlib import Path
def main(path):return next(line for line in Path(path).read_text().splitlines()if line.split()[2]=='main.main')
assert main('hash.log')!=main('prefix-hash.log'),'an unreferenced member in a captured prefix was omitted from main identity'
PY2
cat >main.soma <<'SOMA'
Definition main:=true.
SOMA
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
python3 - <<'PY2'
from pathlib import Path
assert not Path('native/main.assembly').exists()
assert not Path('native/native_assemblies.manifest').exists()
PY2
printf '%s\n' 'PASS: checked dependencies/kinds/names/modules, scope provenance, trusted assumptions, natural local functor Weak ownership, fingerprints and cleanup.' 
