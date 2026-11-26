#!/usr/bin/env bash
# Source owns the checked lexical module and public destructuring pattern.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 40 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
type owner={ bytes:bytes; mutable calls:int }
let prepared=ref 0
let failure=Failure "assembly leaf"
let fail_prepare=ref false
let context:string Lwt.key=Lwt.new_key()
let observe=ref(fun (_:owner) (_:string)->())
let response=ref(Lwt.return "ready")
let create()=incr prepared;if !fail_prepare then raise failure;{bytes=Bytes.make 1048576 'x';calls=0}
let invoke owner text=owner.calls<-owner.calls+1;(!observe)owner text;!response
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "Target.owner".
OCaml Native External Value create : unit -> owner := "Target.create".
OCaml Native External Value invoke : owner -> string -> promise string := "Target.invoke".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native OCaml.
From Stdlib Require Import Strings.String.
Import target.
Local Open Scope string_scope.
Definition body := Native.Export (
 Native.Bind (Native.Call_callback create tt) (fun create =>
 Native.Bind (Native.Call_callback invoke tt) (fun invoke =>
 Native.Invoke create (fun owner =>
 Native.Return (owner,((fun text => invoke owner text),("label","label"))))))).
Definition main := body.
Fail OCaml Native Assembly main As "selected".
Fail OCaml Native Assembly body As "(owner, run) ; failwith bad".
Fail OCaml Native Assembly body As "(same, (same, (x,y)))".
Fail OCaml Native Assembly body As "(owner,run,label)".
Fail OCaml Native Assembly body As "((first,second),rest)".
OCaml Native Assembly body As "(held, (run, (first_label, second_label)))".
Fail OCaml Native Assembly body As "duplicate".
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
import hashlib,shlex
from pathlib import Path
rows=Path('native/native_assemblies.manifest').read_text().splitlines();assert rows[0]=='soma-native-assemblies-v1'
row=shlex.split(rows[1]);symbol,source,source_hash,name,digest,program,interface,bindings,layout,contract=row
assert source_hash==hashlib.sha256(Path(source).read_bytes()).hexdigest()
assert digest==hashlib.sha256(Path('native',name).read_bytes()).hexdigest()
for path,expected in [('prog.ml',program),('prog.mli',interface),('soma_bindings.ml',bindings)]:assert hashlib.sha256(Path('native',path).read_bytes()).hexdigest()==expected
assert next(line.split()[0]for line in Path('hash.log').read_text().splitlines()if line.split()[2]==symbol)==contract
assumptions={a for line in Path('hash.log').read_text().splitlines()if'  assumes 'in line for a in line.split('  assumes ',1)[1].split(', ')}
assert assumptions<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},assumptions
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,target.ml} .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
module Original=struct module Build()=struct
 let held=Target.create()
 let run text=Target.invoke held text
 let first_label="label"and second_label="label"
end end
module Current=struct module Build()=struct
ML
cat native/main.assembly >>check.ml
cat >>check.ml <<'ML'
end end
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let before= !Target.prepared in
 let module Old=Original.Build()in let module New=Current.Build()in
 require "one initialization per module"(!Target.prepared=before+2);
 let label_matrix a b=(a==b)in
 require "literal pooling matrix"(label_matrix Old.first_label Old.second_label=label_matrix New.first_label New.second_label);
 let text=String.make 1048576 't'and fault=Failure "assembly callback"in
 let ready=Lwt.return text and pending,wake=Lwt.task()in let canceled=ref 0 in Lwt.on_cancel pending(fun()->incr canceled);
 List.iter(fun response->Target.response:=response;
  List.iter(fun(owner,run)->Target.observe:=(fun actual value->require "borrowed owner and input"(actual==owner&&value==text);require "caller context"(Lwt.get Target.context=Some "caller"));
   require "exact provider promise"(Lwt.with_value Target.context(Some "caller")(fun()->run text)==response))
   [Old.held,Old.run;New.held,New.run]) [ready;pending;Lwt.fail fault];
 Target.observe:=(fun _ _->());Target.response:=pending;Lwt.cancel(New.run text);require "cancellation forwarded"(!canceled=1);ignore(Sys.opaque_identity wake);
 Target.observe:=(fun _ _->raise fault);require "same synchronous exception"(try ignore(New.run text);false with error->error==fault);
 Target.observe:=(fun _ _->());Target.response:=ready;
 let measure f=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(f text))done;Gc.allocated_bytes()-.before in
 require "exact public call allocation"(measure Old.run=measure New.run);
 let lifetime before=
  let weak=Weak.create 1 in
  let[@inline never] prepare()=if before then(let module V=Original.Build()in Weak.set weak 0(Some V.held);V.run)
    else(let module V=Current.Build()in Weak.set weak 0(Some V.held);V.run)in
  let[@inline never] retain()=let f=prepare()in collect();require "public closure retains original owner"(Weak.check weak 0);ignore(Sys.opaque_identity f)in
  retain();collect();Weak.check weak 0 in
 require "original owner naturally releases"(not(lifetime true));
 require "assembled owner naturally releases"(not(lifetime false));
 Target.fail_prepare:=true;
 require "initialization fault unchanged"(try let module V=Current.Build()in ignore(Sys.opaque_identity V.run);false with error->error==Target.failure);
 print_endline "PASS: Source assembly initialization, public objects/literals, promises/context/cancellation/faults, exact call allocation and natural Weak ownership."
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml check.ml
 "./check-$compiler"
done
# Layout names are part of the checked semantic and native ABI identities.
cp hash.log baseline-hashes
cp native/native_abi.manifest baseline-abi
sed -i.bak 's/(held, (run, (first_label, second_label)))/(held, (invoke, (first_label, second_label)))/' main.soma
soma extract main.soma -no-soma-prelude -o renamed >rename.log 2>&1
soma hash main.soma -no-soma-prelude >renamed-hashes
python3 - <<'PY'
from pathlib import Path
def hashes(p):return {s.split()[2]:s.split()[0]for s in Path(p).read_text().splitlines()}
a,b=hashes('baseline-hashes'),hashes('renamed-hashes')
assert a['main.body']!=b['main.body']and a['main.main']!=b['main.main']
assert Path('baseline-abi').read_bytes()!=Path('renamed/native_abi.manifest').read_bytes()
PY
# Removing a declaration cleans only artifacts that still match producer hashes.
cp main.soma annotated.soma
grep -v 'OCaml Native Assembly' annotated.soma >main.soma
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
test ! -e native/main.assembly
test ! -e native/native_assemblies.manifest
cp annotated.soma main.soma
soma extract main.soma -no-soma-prelude -o native >restore.log 2>&1
printf '\n(* user edit *)\n' >>native/main.assembly
cp native/main.assembly edited.assembly
grep -v 'OCaml Native Assembly' annotated.soma >main.soma
soma extract main.soma -no-soma-prelude -o native >preserve.log 2>&1
cmp edited.assembly native/main.assembly

# A scalar export retains unrestricted generic inputs and physical identities.
mkdir generic
cat >generic/main.soma <<'SOMA'
From Soma Require Import Native OCaml.
Set Universe Polymorphism.
Definition body {A : Type} (value : A) := Native.Export (Native.Return value).
Definition main := @body.
OCaml Native Assembly body As "identity".
SOMA
(cd generic && soma extract main.soma -no-soma-prelude -o native) >generic.log 2>&1
cat generic/native/main.assembly >generic/check.ml
cat >>generic/check.ml <<'ML'
let ()=
 assert(identity true);assert(identity "ok"="ok");
 let f x=x and data=Bytes.make 1048576 'x' in
 assert(identity f==f);assert(identity data==data)
ML
for compiler in ocamlopt ocamlc;do
 (cd generic && ocamlfind "$compiler" -package lwt -linkpkg -w -a -I native -o check native/soma_effect.ml check.ml && ./check)
done

# Native flat products retain their arities instead of becoming nested pairs.
mkdir products
cat >products/main.soma <<'SOMA'
From Soma Require Import Native OCaml.
Definition body := Native.Export (Native.Return
 (Native.Triple 1 true 3,
  (Native.Quadruple 4 true 6 false, Native.Quintuple 8 false 10 true 12))).
Definition main := body.
Fail OCaml Native Assembly body As "((a,(b,c)),rest)".
OCaml Native Assembly body As "((a,b,c),((d,e,f,g),(h,i,j,k,l)))".
SOMA
(cd products && soma extract main.soma -no-soma-prelude -o native) >products.log 2>&1
cat products/native/main.assembly >products/check.ml
cat >>products/check.ml <<'ML'
let ()=assert(a=1&&b&&c=3&&d=4&&e&&f=6&&not g&&h=8&&not i&&j=10&&k&&l=12)
ML
for compiler in ocamlopt ocamlc;do
 (cd products && ocamlfind "$compiler" -package lwt -linkpkg -w -a -I native -o check native/soma_effect.ml check.ml && ./check)
done

# A record pattern must name the complete, runtime-retained checked record.
mkdir records
cat >records/producer.soma <<'SOMA'
Record state := State { count:nat; ready:bool }.
Record proof_state := ProofState { evidence:True; data:nat }.
Record type_state := TypeState { shape:Type; payload:shape }.
Definition main := tt.
SOMA
cat >records/schema.definition <<'SOMA'
From Soma Require Import Native.
Import producer.
OCaml Native Record Alias state := producer.state As "Target.state".
SOMA
cat >records/main.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import schema producer.
Definition wrong := Native.Export (Native.Return (1,true)).
Definition body := Native.Export (Native.Return (State 7 true)).
Definition main := body.
Fail OCaml Native Assembly wrong As "other".
Fail OCaml Native Assembly producer.main As "other".
Fail OCaml Native Assembly body As "{ Target.count }".
Fail OCaml Native Assembly body As "{ Other.count; ready }".
OCaml Native Assembly body As "{ Target.count; ready }".
SOMA
(cd records && soma extract main.soma -no-soma-prelude -o native) >records.log 2>&1
cat >records/target.ml <<'ML'
type state={count:Soma_nat.nat;ready:bool}
ML
cat records/native/main.assembly >records/check.ml
cat >>records/check.ml <<'ML'
let ()=assert(ready);assert(count=7)
ML
for compiler in ocamlopt ocamlc;do
 (cd records && ocamlfind "$compiler" -package lwt -linkpkg -w -a -I native -o check native/soma_nat.ml target.ml native/soma_record_*.ml native/soma_effect.ml check.ml && ./check)
done
cat >records/main.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import producer.
Definition body := Native.Export (Native.Return (ProofState I 7)).
Definition main := body.
Fail OCaml Native Assembly body As "{ Producer.evidence; data }".
SOMA
(cd records && soma check main.soma -no-soma-prelude) >proof-record.log 2>&1
cat >records/main.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import producer.
Definition body := Native.Export (Native.Return (TypeState nat 7)).
Definition main := body.
Fail OCaml Native Assembly body As "{ Producer.shape; payload }".
SOMA
(cd records && soma check main.soma -no-soma-prelude) >type-record.log 2>&1
echo 'PASS: assembly shape checking, generics, records, erased fields and producer-owned stale cleanup.'
