#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?;if [ "$rc" != 0 ];then tail -n 65 "$WORK"/*.log 2>/dev/null||true;fi;rm -rf "$WORK"' EXIT
ocaml(){ opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }
mkdir "$WORK/app"
cp "$HERE"/examples/example_projects/native_parametric_callables/* "$WORK/app/"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
python3 - "$WORK" <<'PY'
from pathlib import Path
import hashlib,shlex,sys
w=Path(sys.argv[1]);out=w/'native';rows=[shlex.split(s)for s in(out/'native_callables.manifest').read_text().splitlines()[1:]]
assert len(rows)==5
seen=set()
for line in(w/'hash').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
for symbol,source,digest,name,product in rows:
 assert hashlib.sha256((w/'app'/source).read_bytes()).hexdigest()==digest
 assert hashlib.sha256((out/name).read_bytes()).hexdigest()==product
 assert 'Obj.'not in(out/name).read_text()
assert 'native-parametric-callable'in(out/'native_abi.manifest').read_text()
assert 'Obj.'not in(out/'soma_bindings.ml').read_text()
PY
cat > "$WORK/native/probe.ml" <<'ML'
let ensure name value=if not value then failwith name
let weak value=let w=Weak.create 1 in Weak.set w 0(Some value);w
let ()=
 let label=Bytes.to_string(Bytes.make 997 'l')and input=ref 13 and output=Bytes.create 1013 in
 let calls=ref[]in
 let target ~label:given value=calls:=(given==label,value==input)::!calls;output in
 ensure"raw callable identity"(Prog.pass target==target);
 ensure"generic labels/borrowed arguments/result"(Prog.invoke target label input==output&& !calls=[true,true]);
 ensure"concrete instance"(Prog.invoke_bool(fun ~label:_ x->not x)"bool"true=false);
 let pair="borrowed",true in
 ensure"product type-argument identity"(Prog.invoke_pair(fun ~label:_ x->x)"pair"pair==pair);
 let nested s=s="yes"in
 ensure"nested schema argument identity"(Prog.invoke_schema(fun ~label:_ x->x)"nested"nested==nested);
 let fn x=x^"!"in
 ensure"arrow type-argument identity"(Prog.invoke_arrow(fun ~label:_ x->x)"arrow"fn==fn);
 let reason=Failure"generic callable synchronous throw"in
 ensure"synchronous exception identity"(try ignore(Prog.invoke(fun ~label:_ _->raise reason)label input);false with e->e==reason);
 let stages=ref 0 and tail_calls=ref 0 in
 let tail value=incr tail_calls;ensure"tail argument identity"(value==input);output in
 let staged ~label:actual=incr stages;ensure"partial label identity"(actual==label);tail in
 let partial=Prog.partial staged label in
 ensure"partial application exact stage"(partial==tail&& !stages=1&& !tail_calls=0);
 ensure"resume identity"(Prog.resume partial input==output&& !stages=1&& !tail_calls=1);
 let key=Lwt.new_key()and pending,wake=Lwt.task()in
 let tokens=[ref 1;ref 2]and context=ref 71 and delimiter=Some '|'in
 let callback given=ensure"callback argument identity"(given==context);ensure"callback context"(Lwt.get key=Some 73);pending in
 let redirect ~persist ~delimiter:actual items scope body=
  ensure"labelled generic redirect arguments"(persist&&actual==delimiter&&items==tokens&&scope==context);
  ensure"callback identity"(body==callback);body scope in
 let answer=Lwt.with_value key(Some 73)(fun()->Prog.redirect_with redirect true delimiter tokens context callback)in
 ensure"raw redirect promise identity"(answer==pending);Lwt.wakeup wake 17;
 ensure"redirect completion"(Lwt.state answer=Lwt.Return 17);
 let pending,_=Lwt.task()in
 let answer=Prog.redirect_with(fun ~persist:_ ~delimiter:_ _ scope body->body scope)false None tokens context(fun _->pending)in
 Lwt.cancel answer;ensure"cancellation propagation"(Lwt.state pending=Lwt.Fail Lwt.Canceled);
 let rejected=Lwt.fail reason in
 let answer=Prog.redirect_with(fun ~persist:_ ~delimiter:_ _ _ _->rejected)false None tokens context callback in
 ensure"rejected promise identity"(answer==rejected);
 ensure"redirect throw phase/identity"(try ignore(Prog.redirect_with(fun ~persist:_ ~delimiter:_ _ _ _->raise reason)false None tokens context callback);false with e->e==reason);
 print_endline"PASS: generic labelled callables: raw aliases, labels, arrow types, exact partial stages, callback/promise identities, synchronous throws, rejection, cancellation and Lwt context"
let ()=
 let key=Lwt.new_key()and stages=ref[]in
 let label=Bytes.to_string(Bytes.make 991 'l')and text=Bytes.to_string(Bytes.make 997 't')in
 let reason=Failure"concrete returned function fault"in
 let tail argument=
  ensure"concrete returned function input alias"(argument==text);
  stages:=("tail",Lwt.get key)::!stages;true in
 let target ~label:given selected=
  ensure"concrete descriptor borrowed label/bool"(given==label&&selected);
  stages:=("target",Lwt.get key)::!stages;tail in
 let returned=Lwt.with_value key(Some 101)(fun()->Prog.invoke_function target label true)in
 ensure"concrete function result physical identity"(returned==tail);
 ensure"concrete Apply stops before returned function"(!stages=["target",Some 101]);
 let result=Lwt.with_value key(Some 202)(fun()->returned text)in
 ensure"returned function executes in caller context"(result&& !stages=["tail",Some 202;"target",Some 101]);
 let throw_tail _=raise reason in
 let returned=Prog.invoke_function(fun ~label:_ _->throw_tail)label false in
 ensure"throwing returned function identity and deferred stage"(returned==throw_tail);
 ensure"returned function throw identity"(try ignore(returned text);false with e->e==reason);
 ensure"concrete Apply immediate target throw"(try ignore(Prog.invoke_function(fun ~label:_ _->raise reason)label false);false with e->e==reason);
 let calls=ref[]in
 let last flag=calls:=("last",Lwt.get key)::!calls;if flag then text else label in
 let middle argument=
  ensure"curried returned function argument alias"(argument==text);
  calls:=("middle",Lwt.get key)::!calls;last in
 let make ~label:given _=
  ensure"curried target label alias"(given==label);
  calls:=("make",Lwt.get key)::!calls;middle in
 let returned=Lwt.with_value key(Some 303)(fun()->Prog.invoke_curried_function make label true)in
 ensure"curried result identity and initial partial stage"(returned==middle&& !calls=["make",Some 303]);
 let partially=Lwt.with_value key(Some 404)(fun()->returned text)in
 ensure"curried result next partial identity/stage"(partially==last&& !calls=["middle",Some 404;"make",Some 303]);
 let result=Lwt.with_value key(Some 505)(fun()->partially true)in
 ensure"curried result final alias/context/stage"(result==text&& !calls=["last",Some 505;"middle",Some 404;"make",Some 303]);
 print_endline"PASS: concrete Apply function/curried-function results preserve raw identity, exact partial stages, context, aliases and target/deferred throws"
let ()=
 let spec=ref 1 and args=[Bytes.to_string(Bytes.make 991 'a')] in
 let number=Bytes.to_string(Bytes.make 997 '3') in
 let target ?(stop=false) ?numeric actual_spec actual_args=
  ensure"optional call borrowed aliases"(actual_spec==spec&&actual_args==args);
  stop,numeric in
 ensure"omitted optional arguments"(Prog.invoke_options target None None spec args=(false,None));
 let stop,numeric=Prog.invoke_options target (Some true)(Some number)spec args in
 ensure"supplied optional arguments"(stop&&Option.get numeric==number);
 let reason=Failure"optional callable failure"in
 let throw ?stop:_ ?numeric:_ _ _=raise reason in
 ensure"optional call throws synchronously"(try
   ignore(Prog.invoke_options throw None (Some number)spec args);false with e->e==reason);
 print_endline"PASS: exact optional callable defaults, supplied values, aliases and synchronous exception identity"
let[@inline never] lifetime invoke()=
 let owner=Bytes.create 2048 in
 let target ~label:_ value=ignore(Sys.opaque_identity owner);value in
 let w=weak owner in let value=invoke target "label" "value"in
 Gc.full_major();Gc.full_major();let kept=Weak.check w 0 in ignore(Sys.opaque_identity value);kept
let ()=ensure"consumed callable owner lifetime"(lifetime(fun f label x->f ~label x)()=lifetime Prog.invoke());
 print_endline"PASS: consumed generic callable owner Weak lifetime"
ML
python3 - "$WORK/native" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);mods=sorted(f.stem for f in p.glob('*.ml')if f.stem!='soma_main')
(p/'dune').write_text('(executable (name probe) (modes exe byte) (modules '+' '.join(mods)+') (libraries lwt) (flags (:standard -w -a)))\n')
PY
ocaml dune build --root "$WORK/native" --profile release -j2 probe.exe probe.bc > "$WORK/build.log" 2>&1
ocaml "$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"
mkdir "$WORK/second"
cp "$WORK/app/functions.definition" "$WORK/second/"
printf 'From Soma Require Native.\nImport functions.\nDefinition main:=@functions.apply.\n' > "$WORK/second/main.soma"
"$SOMA" extract "$WORK/second/main.soma" -o "$WORK/other" > "$WORK/other.log" 2>&1
python3 - "$WORK" <<'PY'
from pathlib import Path
import sys
w=Path(sys.argv[1]);a={p.name:p.read_bytes()for p in(w/'native').glob('soma_callable_*.ml')};b={p.name:p.read_bytes()for p in(w/'other').glob('soma_callable_*.ml')};assert a==b
p=w/'app/functions.definition';p.write_text(p.read_text().replace('(label:string)','(description:string)'))
PY
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/changed-hash"
if cmp -s "$WORK/hash" "$WORK/changed-hash";then echo 'generic labels did not change hashes' >&2;exit 1;fi
negative(){
 local name=$1 declaration=$2 source=$3 pattern=$4
 mkdir "$WORK/$name"
 cp "$HERE"/examples/example_projects/native_parametric_callables/functions.definition "$WORK/$name/"
 printf 'From Soma Require Native.\nImport functions.\n%s\n' "$declaration" > "$WORK/$name/bad.definition"
 printf 'From Soma Require Native.\nImport functions bad.\n%s\n' "$source" > "$WORK/$name/main.soma"
 if "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/native" > "$WORK/$name.log" 2>&1;then echo "accepted $name" >&2;exit 1;fi
 grep -q "$pattern" "$WORK/$name.log"
}
negative optional_nonoption 'OCaml Native Callable bad Optional flag:=forall(flag:bool),unit->bool.' 'Definition main:=bad.bad.' 'must have type option'
negative optional_unknown 'OCaml Native Callable bad Optional absent:=forall(flag:option bool),unit->bool.' 'Definition main:=bad.bad.' 'exactly once'
negative optional_wrong_apply 'OCaml Native Apply bad:parse_options unit bool->bool->option string->unit->list string->bool.' 'Definition main:=bad.bad.' 'signature differs'
negative proof_parameter 'OCaml Native Callable bad:=forall(A:Prop),A->A.' 'Definition main:=@bad.bad.' 'named Type or Set'
negative strict_proof_parameter 'OCaml Native Callable bad:=forall(A:SProp),A->A.' 'Definition main:=@bad.bad.' 'named Type or Set'
negative duplicate 'OCaml Native Callable bad:=forall(A A:Type),A->A.' 'Definition main:=@bad.bad.' 'parameters must be distinct'
negative type_after_value 'OCaml Native Callable bad:=string->forall(A:Type),A->A.' 'Definition main:=@bad.bad.' 'must precede values'
negative higher_rank 'OCaml Native Callable bad:=forall(A:Type),(forall(B:Type),B->B)->A.' 'Definition main:=@bad.bad.' 'must be monomorphic'
negative dependent 'OCaml Native Callable bad:=forall(n:nat),{m:nat|m=n}.' 'Definition main:=@bad.bad.' 'depends on a value'
negative wrong_result 'OCaml Native Apply bad:forall(A B:Type),transform A B->string->A->A.' 'Definition main:=@bad.bad.' 'signature differs'
negative concrete_wrong 'OCaml Native Apply bad:transform string bool->string->string->string.' 'Definition main:=@bad.bad.' 'signature differs'
negative concrete_function_wrong 'OCaml Native Apply bad:transform bool(string->bool)->string->bool->(string->string).' 'Definition main:=@bad.bad.' 'signature differs'
negative confused '' 'Definition main(value:transform string bool):transform bool string:=value.' 'has type\|expected\|cannot be applied'
negative inspection '' 'Definition main{A B:Type}(value:transform A B):nat:=match value with Native.Native_family id=>id end.' 'cannot be inspected'
echo 'PASS: generic callable shared ABI/provenance/hash, parameter separation, checked signatures and malformed declarations'

mkdir "$WORK/monomorphic"
cp "$HERE"/examples/example_projects/native_parametric_callables/functions.definition "$WORK/monomorphic/"
cat > "$WORK/monomorphic/fixture.definition" <<'SOMA'
From Soma Require Native.
Import functions.
OCaml Native External Callback make:forall(A:Type),unit->transform A A:= "Fixture.make".
SOMA
printf 'let make () ~label:_ x=not x\n' > "$WORK/monomorphic/fixture.ml"
printf 'From Soma Require Native.\nImport functions fixture.\nDefinition main:=@fixture.make.\n' > "$WORK/monomorphic/main.soma"
"$SOMA" extract "$WORK/monomorphic/main.soma" -o "$WORK/monomorphic/native" > "$WORK/monomorphic.log" 2>&1
if ocaml dune build --root "$WORK/monomorphic/native" --profile release -j2 >> "$WORK/monomorphic.log" 2>&1;then echo 'accepted monomorphic generic implementation' >&2;exit 1;fi
grep -q 'less general\|not as general\|polymorphic' "$WORK/monomorphic.log"
echo 'PASS: universal descriptor rejects a boolean-only native implementation'
mkdir "$WORK/wronglabel"
cp "$WORK/monomorphic/functions.definition" "$WORK/wronglabel/"
cp "$WORK/monomorphic/fixture.definition" "$WORK/wronglabel/"
cp "$WORK/monomorphic/main.soma" "$WORK/wronglabel/"
printf 'let make () ~description:_ x=x\n' > "$WORK/wronglabel/fixture.ml"
"$SOMA" extract "$WORK/wronglabel/main.soma" -o "$WORK/wronglabel/native" > "$WORK/wronglabel.log" 2>&1
if ocaml dune build --root "$WORK/wronglabel/native" --profile release -j2 >> "$WORK/wronglabel.log" 2>&1;then echo 'accepted wrong labelled generic implementation' >&2;exit 1;fi
grep -q 'description\|label' "$WORK/wronglabel.log"
echo 'PASS: generic native implementation with wrong OCaml labels is rejected'
