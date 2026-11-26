#!/usr/bin/env bash
# Typed Source partial applications publish complete compiler-owned ML/Mli.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 35 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type owner={bytes:bytes}
let initialized=ref 0
let weak=Weak.create 1
let fault=Failure "public assembly"
let context:string Lwt.key=Lwt.new_key()
let fail=ref false
let response=ref(Lwt.return "ready")
let observe=ref(fun (_:owner) (_:string)->())
let create()=incr initialized;if !fail then raise fault;let v={bytes=Bytes.make 1048576 'x'}in Weak.set weak 0(Some v);v
let invoke owner text=(!observe)owner text;!response
ML
cat >target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "Target.owner".
OCaml Native External Callback create : unit -> owner := "Target.create".
OCaml Native External Value invoke : owner -> string -> promise string := "Target.invoke".
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
From Stdlib Require Import Strings.String.
Import target.
Definition owner := Native.Export(Native.Call_callback create tt).
Definition wrong := true.
Definition unused := false.
Definition keep{A:Type}(value:A) := value.
Definition run_with(receiver:target.owner)(text:string) := Native.Export(
 Native.Bind(Native.Call_callback invoke tt)(fun call=>Native.tail_invoke(fun _=>call receiver text))).
Definition main := ((owner,run_with),(@keep,wrong)).
Fail OCaml Native Public Assembly run_with With [Apply "run" := run_with With [owner]].
Fail OCaml Native Public Assembly main With [Apply "run" := run_with With [wrong]].
Fail OCaml Native Public Assembly main With [Apply "run" := run_with With [unused]].
Fail OCaml Native Public Assembly main With [Apply "owner" := run_with With [owner]].
Fail OCaml Native Public Assembly main With [Apply "run;bad" := run_with With [owner]].
Fail OCaml Native Public Assembly main With [Apply "run" := run_with With [owner];Apply "run" := run_with With [owner]].
OCaml Native Public Assembly main With [Apply "run" := run_with With [owner]].
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
rows=Path('native/native_assemblies.manifest').read_text().splitlines();assert rows[0]=='soma-native-assemblies-v1'
assert len(rows)==3
for row in rows[1:]:
 symbol,source,source_hash,file,digest,program,interface,bindings,layout,contract=shlex.split(row)
 for path,h in [(source,source_hash),('native/'+file,digest),('native/prog.ml',program),('native/prog.mli',interface),('native/soma_bindings.ml',bindings)]:assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==h
 assert next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]==symbol)==contract
 assert symbol=='main.main'
for l in Path('hash.log').read_text().splitlines():
 a=set(l.split('  assumes ',1)[1].split(', '))if'  assumes 'in l else set()
 assert a<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},a
PY
(cd native&&dune build --profile release -j2)>build.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,target.ml,soma_bindings.ml} .
# Compile the producer's complete public implementation and interface as-is.
cp native/main.assembly published.ml
cp native/main.assembly-interface published.mli
cat >standalone.ml <<'ML'
let ()=assert(Published.keep true);assert(Published.keep "generic"="generic");assert(Published.run "value"== !Target.response)
ML
cat >check.ml <<'ML'
let require name b=if not b then failwith name
module Original=struct module Build()=struct
ML
cat native/prog.ml >>check.ml
printf '\nlet run = run_with owner0\nend end\nmodule Current=struct module Build()=struct\n' >>check.ml
cat native/main.assembly >>check.ml
cat >>check.ml <<'ML'
end end
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let before= !Target.initialized in let module Old=Original.Build()in let module New=Current.Build()in
 require "one preparation per module"(!Target.initialized=before+2);
 let text=String.make 1048576 's'and data=Bytes.make 1048576 'b'and f x=x in
 require "existing generic API retains all types"(New.keep text==text&&New.keep data==data&&New.keep f==f&&New.keep true);
 let pending,wake=Lwt.task()and fault=Failure"public call"in let canceled=ref 0 in Lwt.on_cancel pending(fun()->incr canceled);
 List.iter(fun response->Target.response:=response;
  List.iter(fun(owner,run)->Target.observe:=(fun actual input->require "borrowed owner/input and caller context"(actual==owner&&input==text&&Lwt.get Target.context=Some"caller"));
   require "exact returned promise"(Lwt.with_value Target.context(Some"caller")(fun()->run text)==response))
   [Old.owner0,Old.run;New.owner0,New.run]) [Lwt.return text;pending;Lwt.fail fault];
 Target.observe:=(fun _ _->());Target.response:=pending;Lwt.cancel(New.run text);require "cancellation reaches original promise"(!canceled=1);ignore(Sys.opaque_identity wake);
 Target.observe:=(fun _ _->raise fault);require "same synchronous exception"(try ignore(New.run text);false with error->error==fault);
 Target.observe:=(fun _ _->());Target.response:=Lwt.return text;
 let measure run=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(run text))done;Gc.allocated_bytes()-.before in
 require "exact public call allocation"(measure Old.run=measure New.run);
 let lifetime old=
  let[@inline never] prepare()=if old then(let module V=Original.Build()in V.run)else(let module V=Current.Build()in V.run)in
  let[@inline never] retain()=let f=prepare()in collect();require "partial closure retains original owner"(Weak.check Target.weak 0);ignore(Sys.opaque_identity(f text))in
  retain();collect();Weak.check Target.weak 0 in
 require "original owner naturally releases"(not(lifetime true));require "published owner naturally releases"(not(lifetime false));
 Target.fail:=true;require "preparation fault unchanged"(try let module V=Current.Build()in ignore(Sys.opaque_identity V.run);false with error->error==Target.fault);
 print_endline "PASS: public Source ML/Mli partial applications retain all existing generics, single preparation, original owners/promises/context/faults/cancellation, exact call allocation and natural Weak lifetime."
ML
for compiler in ocamlopt ocamlc;do
 common=(soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_bindings.ml)
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o standalone "${common[@]}" published.mli published.ml standalone.ml
 ./standalone
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o check "${common[@]}" check.ml
 ./check
done
cp hash.log before-hashes
sed -i.bak 's/Apply "run" :=/Apply "published" :=/g' main.soma
soma hash main.soma -no-soma-prelude >after-hashes
python3 - <<'PY'
from pathlib import Path
def read(p):return {l.split()[2]:l.split()[0]for l in Path(p).read_text().splitlines()}
a,b=read('before-hashes'),read('after-hashes');assert a['main.main']!=b['main.main'];assert a['main.run_with']==b['main.run_with']
PY
cp main.soma valid.soma
sed -i.bak 's/Apply "published" :=/Apply "soma_main" :=/g' main.soma
if soma extract main.soma -no-soma-prelude -o collision >collision.log 2>&1;then
 echo 'accepted a public name shadowing an actual extracted value' >&2;exit 1
fi
grep -q 'shadows an existing extracted value' collision.log
cp valid.soma main.soma
grep -v 'OCaml Native Public Assembly' main.soma >plain.soma
mv plain.soma main.soma
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
test ! -e native/main.assembly
test ! -e native/main.assembly-interface
test ! -e native/native_assemblies.manifest
