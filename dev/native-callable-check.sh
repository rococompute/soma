#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 50 "$WORK"/*.log 2>/dev/null||true;fi;rm -rf "$WORK"' EXIT
ocaml() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }
mkdir "$WORK/app"
cp "$HERE"/examples/example_projects/native_callables/* "$WORK/app/"
SOMA_OCAML_BINDINGS_MODULE=Callable_bindings "$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
python3 - "$WORK" <<'PY'
from pathlib import Path
import hashlib,shlex,sys
w=Path(sys.argv[1]);out=w/'native';rows=[shlex.split(s)for s in(out/'native_callables.manifest').read_text().splitlines()[1:]]
assert (out/'native_callables.manifest').read_text().startswith('soma-native-callables-v1\n')
assert len(rows)==3
for symbol,source,source_hash,filename,generated_hash in rows:
 assert hashlib.sha256((w/'app'/source).read_bytes()).hexdigest()==source_hash
 assert hashlib.sha256((out/filename).read_bytes()).hexdigest()==generated_hash
 assert 'Obj.'not in(out/filename).read_text()
assert not(out/'functions.ml').exists()
allowed={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'};seen=set()
for line in(w/'hash').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split())
assert seen==allowed,seen
print('PASS: defined callable schemas, typed generated modules and exact source/product/assumption provenance')
PY
cat > "$WORK/native/probe.ml" <<'ML'
let ensure label value=if not value then failwith label
let ()=
 let calls=ref[]in let cwd=Bytes.to_string(Bytes.of_string"/cwd")and path=Bytes.to_string(Bytes.of_string"file")in
 let normalize ~cwd:actual_cwd given=calls:=(actual_cwd==cwd,given==path)::!calls;given in
 ensure"opaque callable identity"(Prog.pass normalize==normalize);
 ensure"labelled callable argument/result identity"(Prog.normalize_with normalize cwd path==path&& !calls=[true,true]);
 let reason=Failure"labelled callable"in
 ensure"exception identity"(try ignore(Prog.normalize_with(fun ~cwd:_ _->raise reason)cwd path);false with e->e==reason);
 let pair ~left ~right=left^right in ensure"two labelled arguments"(Prog.pair_with pair "L" "R"="LR");
 let key=Lwt.new_key()in let pending,wake=Lwt.task()in
 let callback()=ensure"callback scope"(Lwt.get key=Some 73);pending in
 let target body=ensure"callback physical identity"(body==callback);body()in
 let result=Lwt.with_value key(Some 73)(fun()->Prog.invoke_with target callback)in
 ensure"borrowed promise identity"(result==pending);Lwt.wakeup wake();ensure"promise completion"(Lwt.state result=Lwt.Return());
 let pending,_=Lwt.task()in let result=Prog.invoke_with(fun body->body())(fun()->pending)in Lwt.cancel result;
 ensure"promise cancellation"(Lwt.state pending=Lwt.Fail Lwt.Canceled);
 print_endline"PASS: native labelled arguments, function/callback/result/promise identities, throw phases, cancellation and dynamic context"
let weak value=let w=Weak.create 1 in Weak.set w 0(Some value);w
let[@inline never] target_probe invoke ()=
 let owner=Bytes.create 2048 in let target ~cwd:_ _=ignore(Sys.opaque_identity owner);"result"in
 let w=weak owner in let value=invoke target "/cwd" "file"in Gc.full_major();let kept=Weak.check w 0 in
 ignore(Sys.opaque_identity value);kept
let raw target cwd path=target ~cwd path
let ()=ensure"consumed native callable owner releases like direct application"(target_probe raw()=target_probe Prog.normalize_with())
ML
python3 - "$WORK/native" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);mods=sorted(f.stem for f in p.glob('*.ml')if f.stem!='soma_main')
(p/'dune').write_text('(executable (name probe) (modes exe byte) (modules '+' '.join(mods)+') (libraries lwt) (flags (:standard -w -a)))\n')
PY
(cd "$WORK/native"&&ocaml dune build --profile release -j2 probe.exe probe.bc) > "$WORK/build.log" 2>&1
"$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"
# Label metadata must invalidate the logical program even with equal domains.
sed 's/forall (cwd : string)/forall (directory : string)/' "$WORK/app/functions.definition" > "$WORK/changed"
mv "$WORK/changed" "$WORK/app/functions.definition"
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/changed-hash"
python3 - "$WORK/hash" "$WORK/changed-hash" <<'PY'
from pathlib import Path
import sys
main=lambda p:next(s.split()[0]for s in Path(p).read_text().splitlines()if s.split()[2]=='main.main')
assert main(sys.argv[1])!=main(sys.argv[2])
PY
negative() {
 local name=$1 text=$2 expected=$3
 mkdir "$WORK/$name"
 printf 'From Soma Require Native.\n%s\n' "$text" > "$WORK/$name/decl.definition"
 printf 'Import decl.\nDefinition main:=tt.\n' > "$WORK/$name/main.soma"
 if "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/native" > "$WORK/$name.log" 2>&1;then echo "accepted $name" >&2;exit 1;fi
 grep -q "$expected" "$WORK/$name.log"
}
negative higher_rank 'OCaml Native Callable t:=(forall A:Type,A->A)->string.' 'must be monomorphic'
negative dependent 'OCaml Native Callable t:=forall n:nat,{m:nat | m=n}.' 'depends on a value'
negative nonfunction 'OCaml Native Callable t:=string.' 'at least one argument'
negative wrongresult 'OCaml Native Callable t:=string->string. OCaml Native Apply f:t->string->bool.' 'signature differs'
negative wrongargument 'OCaml Native Callable t:=string->string. OCaml Native Apply f:t->bool->string.' 'signature differs'
negative nontarget 'OCaml Native Apply f:string->string.' 'declared native callable'
mkdir "$WORK/inspection"
cp "$HERE/examples/example_projects/native_callables/functions.definition" "$WORK/inspection/"
printf 'From Soma Require Native.\nImport functions.\nDefinition main(f:normalizer):nat:=match f with Native.Native_handle id=>id end.\n' > "$WORK/inspection/main.soma"
if "$SOMA" extract "$WORK/inspection/main.soma" -o "$WORK/inspection/native" > "$WORK/inspection.log" 2>&1;then echo 'accepted callable inspection' >&2;exit 1;fi
grep -q 'cannot be inspected' "$WORK/inspection.log"
echo 'PASS: label metadata changes logical hashes and malformed signatures/inspection are rejected'
mkdir "$WORK/ffi"
cp "$HERE/examples/example_projects/native_callables/functions.definition" "$WORK/ffi/"
cat > "$WORK/ffi/caller.definition" <<'SOMA'
From Soma Require Native.
Import functions.
OCaml Native Callback make : unit -> normalizer := "make".
SOMA
printf 'let make () = fun ~cwd path -> cwd ^ path\n' > "$WORK/ffi/caller.ml"
cat > "$WORK/ffi/main.soma" <<'SOMA'
From Soma Require Native.
Import functions caller.
Definition main:=Native.Export(Native.Bind(Native.Call_callback make tt)(fun target=>Native.Call_callback normalize(target,("/cwd","/file")))).
SOMA
"$SOMA" extract "$WORK/ffi/main.soma" -o "$WORK/ffi/native" > "$WORK/ffi.log" 2>&1
(cd "$WORK/ffi/native"&&ocaml dune build --profile release -j2) >> "$WORK/ffi.log" 2>&1
printf 'let make () = fun ~directory path -> directory ^ path\n' > "$WORK/ffi/caller.ml"
"$SOMA" extract "$WORK/ffi/main.soma" -o "$WORK/ffi/bad" > "$WORK/ffi-negative.log" 2>&1
if (cd "$WORK/ffi/bad"&&ocaml dune build --profile release -j2) >> "$WORK/ffi-negative.log" 2>&1;then echo 'accepted wrong native callable label' >&2;exit 1;fi
grep -q 'directory\|cwd' "$WORK/ffi-negative.log"
echo 'PASS: actual native callable type checked across FFI; wrong label rejected'
if [ "${SOMA_TEST_HVF:-0}" = 1 ];then
 mkdir "$WORK/image"
 cp "$HERE/examples/example_projects/native_callables/functions.definition" "$WORK/image/"
 printf '[project]\nname="native_callable_image"\nversion="0.1.0"\n' > "$WORK/image/soma.toml"
 cat > "$WORK/image/caller.definition" <<'SOMA'
From Soma Require Native.
Import functions.
OCaml Native Callback make : unit -> normalizer := "make".
invoke : (unit -> Native.entry string) -> string.
SOMA
 printf 'let make () = fun ~cwd path -> cwd ^ path\nlet invoke f = f ()\n' > "$WORK/image/caller.ml"
 cat > "$WORK/image/main.soma" <<'SOMA'
Require Import Sandbox.
From Soma Require Native.
Import functions caller.
Definition probe:=Native.Export(Native.Bind(Native.Call_callback make tt)(fun target=>Native.Call_callback normalize(target,("/cwd","/file")))).
Definition main:io unit:=
 value<-call(fun _=>invoke(fun _=>probe));;
 if String.eqb value "/cwd/file"then print "native labelled callables in Solo5 verified"else exit 1.
SOMA
 SOMA_MIRAGE_SWITCH=${SOMA_MIRAGE_SWITCH:-kykeon} SOMA_MIRAGE_DIR="$WORK/image-project" \
 SOMA_OCAML_BINDINGS_MODULE=Callable_image_bindings "$SOMA" build "$WORK/image/main.soma" > "$WORK/image-build.log" 2>&1
 timeout 30 opam exec --switch="${SOMA_MIRAGE_SWITCH:-kykeon}" -- solo5-hvt --mem=256 -- "$WORK/image/main.hvt" > "$WORK/image-boot.log" 2>&1
 grep -q 'native labelled callables in Solo5 verified' "$WORK/image-boot.log"
 echo 'PASS: typed labelled callable executes inside actual Solo5'
fi
echo 'native callable schemas: ok'
