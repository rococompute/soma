#!/bin/sh
# Assumption-free native declarations; no package installation or network access.
set -eu
HERE=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d "${TMPDIR:-/tmp}/soma-native-abi.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
ocaml() {
  if [ -n "${SOMA_NATIVE_TEST_SWITCH:-}" ]; then
    opam exec --switch="$SOMA_NATIVE_TEST_SWITCH" -- "$@"
  else
    opam exec -- "$@"
  fi
}
mkdir "$WORK/app"
cp "$HERE"/examples/example_projects/native_abi/*.ml "$HERE"/examples/example_projects/native_abi/*.definition \
  "$HERE"/examples/example_projects/native_abi/*.soma "$HERE"/examples/example_projects/native_abi/*.exp "$WORK/app/"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" >"$WORK/extract.log" 2>&1 || { cat "$WORK/extract.log"; exit 1; }
(cd "$WORK/native" && ocaml dune build --profile release)
[ "$("$WORK/native/_build/default/soma_main.exe")" = 'new native ABI' ]
"$SOMA" hash "$WORK/app/main.soma" >"$WORK/hash"
python3 - "$WORK/hash" "$WORK/native/native_abi.manifest" <<'PY'
import sys
for line in open(sys.argv[1]):
    if '  assumes ' in line:
        names=line.split('  assumes ',1)[1].strip().split(', ')
        assert all(n == 'Corelib.Numbers.Cyclic.Int63.PrimInt63.int' for n in names), line
manifest=open(sys.argv[2]).read()
assert manifest.startswith('soma-native-abi-v1\n')
for op in ('native-type', 'native-callback', 'get ', 'set ', 'build ', 'copy ', 'call '):
    assert op in manifest, (op,manifest)
print('PASS: named imports, record operations, labels, cross-import discrimination and assumption/provenance audits')
PY
# Different logical module paths must not collide after OCaml identifier
# encoding (A__B.x and A.B.x collided under the legacy flattening spelling).
"$SOMA" extract "$WORK/app/namespace_main.soma" -o "$WORK/namespaces" >"$WORK/namespaces.log" 2>&1 || { cat "$WORK/namespaces.log";exit 1; }
(cd "$WORK/namespaces" && ocaml dune build --profile release)
[ "$("$WORK/namespaces/_build/default/soma_main.exe")" = "$(printf 'left:namespace\nright:namespace')" ]
printf '%s\n' 'PASS: nested descriptor namespaces preserve distinct generated wrappers'
# Exported main may be opaque: dependency discovery must still include all
# native declarations rather than silently producing unbound wrappers.
"$SOMA" extract "$WORK/app/opaque_main.soma" -o "$WORK/opaque" >"$WORK/opaque.log" 2>&1 || { cat "$WORK/opaque.log";exit 1; }
(cd "$WORK/opaque" && ocaml dune build --profile release)
[ "$("$WORK/opaque/_build/default/soma_main.exe")" = 'opaque native ABI' ]
printf '%s\n' 'PASS: opaque exported main discovers its native declarations'
# Independent raw native operations form the oracle. Only the wrapper aliases
# below are selected mechanically from the generated declaration comments.
python3 - "$WORK/native/soma_bindings.ml" "$WORK/native/probe.ml" <<'PY'
import re,sys
text=open(sys.argv[1]).read()
assert 'Obj.' not in text
names=dict(re.findall(r'\(\* native fixture\.(\w+) \*\)\s*let (\w+) :',text))
with open(sys.argv[2],'w') as f:
    for name,symbol in names.items(): f.write(f'let {name}=Soma_bindings.{symbol}\n')
PY
cat >> "$WORK/native/probe.ml" <<'ML'
let require message condition=if not condition then failwith message
let root ()=()
let ()=
 let original:Fixture.item={value="a";label="label";root}in
 require "getter alias" (get_value original==original.value);
 require "callback identity" (get_root original==original.root);
 set_value(original,"changed");require "setter alias" (original.value="changed");
 let copied=copy_value(original,"copy")in
 require "copy allocation"(copied!=original);
 require "copy sharing"(copied.label==original.label && copied.root==original.root);
 require "copy mutation extent"(original.value="changed" && copied.value="copy");
 let built=make_item("value",("name",root))in
 require "full build"(built.value="value" && built.label="name" && built.root==root);
 require "labels"(join("left","right")=Fixture.join ~left:"left" "right");
 let sentinel=Failure "sentinel"in
 List.iter(fun invoke->try invoke(original,(fun()->raise sentinel));failwith "missing throw"
   with e->require "exception identity"(e==sentinel))
  [(fun(r,callback)->Fixture.visit r callback);visit];
 let key=Lwt.new_key()in
 Lwt.with_value key(Some 17)(fun()->visit(original,(fun()->require "context"(Lwt.get key=Some 17))));
 let promise,_=Lwt.task()in
 require "promise identity"(pending(original,(fun()->promise))==promise);
 Lwt.cancel promise;require "cancellation"(match Lwt.state promise with Lwt.Fail Lwt.Canceled->true|_->false)
let record_with_weak()=
 let weak=Weak.create 1 in
 let token=ref 42 in Weak.set weak 0(Some token);
 let record:Fixture.item={value="x";label="y";root=(fun()->ignore(Sys.opaque_identity token))}in record,weak
let observer weak()=Gc.full_major();Weak.check weak 0
let observe invoke=
 let record,weak=record_with_weak()in
 invoke(record,observer weak)
let ()=
 let direct=observe(fun(r,callback)->Fixture.inspect r callback) in
 let generated=observe inspect in
 require "weak rooting through tailcall"(direct=generated);
 Printf.printf "weak tailcall: direct=%b generated=%b\n" direct generated;
 let compare_seen invoke=
  let result=ref None in
  let record,weak=record_with_weak()in
  let observe=fun()->result:=Some(observer weak())in
  invoke(record,observe);!result in
 let raw_seen=compare_seen(fun(r,f)->Fixture.visit r f)and generated_seen=compare_seen visit in
 require "weak rooting inside callback"(raw_seen=generated_seen);
 Printf.printf "weak callback: direct=%s generated=%s\n" (match raw_seen with None->"none"|Some b->string_of_bool b)(match generated_seen with None->"none"|Some b->string_of_bool b);
 let returned_weak getter=let record,weak=record_with_weak()in ignore(getter record);weak in
 let after getter=
  let weak=returned_weak getter in
  Gc.full_major();Weak.check weak 0 in
 require "getter provider release"(after(fun r->r.Fixture.value)=after get_value);
 print_endline "PASS: native record identity, callbacks, exceptions, promises and independent weak-rooting comparisons"
ML
# Build both modes independently of the extracted main's own executable stanza.
cat >> "$WORK/native/dune" <<'DUNE'
(executable
 (name probe)
 (modes byte exe)
 (modules probe fixture other soma_bindings soma_nat soma_effect soma_handles)
 (libraries lwt)
 (flags (:standard -w -a)))
DUNE
# Dune requires each source module to belong to just one stanza.
python3 - "$WORK/native/dune" <<'PY'
import sys
p=sys.argv[1];s=open(p).read();s=s[s.index('(executable',s.index('(executable')+1):];open(p,'w').write(s)
PY
(cd "$WORK/native" && ocaml dune build --profile release probe.exe probe.bc)
"$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"
# Same logical descriptor key/body, changed target: the metadata must change
# both program hashes and generated provenance.
sed 's/:= "join"\./:= "join_other"./' "$WORK/app/fixture.definition" >"$WORK/changed"
mv "$WORK/changed" "$WORK/app/fixture.definition"
"$SOMA" hash "$WORK/app/main.soma" >"$WORK/changed-hash"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/changed-native" >"$WORK/changed-extract.log" 2>&1 || { cat "$WORK/changed-extract.log";exit 1; }
python3 - "$WORK/hash" "$WORK/changed-hash" "$WORK/native/native_abi.manifest" "$WORK/changed-native/native_abi.manifest" <<'PY'
import pathlib,sys
def hashes(path):
    return {parts[2]:tuple(parts[:2]) for line in pathlib.Path(path).read_text().splitlines()
            if len(parts:=line.split()) >= 3}
before,after=map(hashes,sys.argv[1:3])
for symbol in ('fixture.join','main.main'):
    assert before[symbol] != after[symbol], ('stale dependent hash',symbol)
original,changed=(pathlib.Path(p).read_bytes() for p in sys.argv[3:5])
assert original != changed and b'join_other' in changed, 'stale native ABI provenance'
print('PASS: declaration target changes invalidate imported and dependent main hashes and generated provenance')
PY
# Symbolic constructors and destructors never act as a native evaluator.
runtime_negative() {
 name=$1; program=$2; expected=$3; phase=${4:-runtime}
 mkdir "$WORK/$name"
 cp "$WORK/app/fixture.ml" "$WORK/app/fixture.definition" "$WORK/$name/"
 printf '%s\n' 'Import fixture.' 'From Soma Require Native.' "$program" >"$WORK/$name/main.soma"
 if ! "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/out" >"$WORK/$name/log" 2>&1; then
   [ "$phase" = extract ] || { cat "$WORK/$name/log";exit 1; }
   rg -q "$expected" "$WORK/$name/log"
   printf 'PASS: rejected %s during extraction\n' "$name"
   return
 fi
 [ "$phase" = runtime ] || { echo "FAIL: $name inspection extracted";exit 1; }
 (cd "$WORK/$name/out" && ocaml dune build --profile release) >>"$WORK/$name/log" 2>&1 || { cat "$WORK/$name/log";exit 1; }
 if "$WORK/$name/out/_build/default/soma_main.exe" >>"$WORK/$name/log" 2>&1; then
   echo "FAIL: $name evaluated a placeholder";exit 1
 fi
 rg -q "$expected" "$WORK/$name/log"
 printf 'PASS: rejected %s at runtime\n' "$name"
}
runtime_negative named_constructor 'Definition main := Native.Export(Native.Call_callback (@Native.Named_callback string unit "fixture" "say") "forged").' 'a named callback requires a native declaration'
runtime_negative handle_constructor 'Definition main := Native.Export(Native.Call_callback fixture.get_value (Native.Native_handle 0)).' 'a native handle requires a native declaration'
runtime_negative handle_inspection 'Definition inspect(item:fixture.item) := match item with Native.Native_handle id => Native.Bind(Native.Nat_decimal id)(fun text=>Native.Call_callback fixture.say text)end. Definition main := Native.Export(Native.Bind(Native.Call_callback fixture.make_item("x",("y",fun _=>tt)))inspect).' 'Native programs and entry points cannot be inspected' extract
runtime_negative callback_inspection 'Definition inspect(c:Native.callback string unit) := match c with Native.Callback _=>Native.Call_callback fixture.say "ordinal"|Native.Named_callback _ name=>Native.Call_callback fixture.say name end. Definition main := Native.Export(inspect fixture.say).' 'Native programs and entry points cannot be inspected' extract
# Negative declarations/signatures remain independent of the valid fixture.
negative() {
 name=$1; declaration=$2; phase=$3; diagnostic=$4
 mkdir "$WORK/$name"
 cp "$WORK/app/fixture.ml" "$WORK/$name/fixture.ml"
 printf '%s\n' 'From Soma Require Native.' 'OCaml Native Type item := "item".' "$declaration" >"$WORK/$name/fixture.definition"
 printf '%s\n' 'Import fixture.' 'From Soma Require Native.' 'Definition main := bad.' >"$WORK/$name/main.soma"
 if "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/out" >"$WORK/$name/log" 2>&1; then
   [ "$phase" = ocaml ] || { echo "FAIL: $name accepted by Soma"; exit 1; }
   if (cd "$WORK/$name/out" && ocaml dune build --profile release) >>"$WORK/$name/log" 2>&1; then
     echo "FAIL: $name accepted by OCaml";exit 1
   fi
 else
   [ "$phase" = soma ] || { cat "$WORK/$name/log";exit 1; }
 fi
 rg -q "$diagnostic" "$WORK/$name/log" || { cat "$WORK/$name/log";exit 1; }
 printf 'PASS: rejected %s\n' "$name"
}
negative immutable 'OCaml Native Set bad : item -> string -> unit := "label".' ocaml 'not mutable'
negative missing_field 'OCaml Native Get bad : item -> string := "absent".' ocaml 'Unbound record field'
negative wrong_signature 'OCaml Native Get bad : item -> bool := "value".' ocaml 'expected of type'
negative incomplete_build 'OCaml Native Build bad : string -> item := "value".' ocaml 'record fields are undefined'
negative duplicate_fields 'OCaml Native Build bad : string -> string -> item := "value" "value".' soma 'record fields must be distinct'
negative malformed_symbol 'OCaml Native Get bad : item -> string := "value;failwith".' soma 'invalid value name'
negative polymorphic 'OCaml Native Callback bad : forall A, A -> A := "same".' soma 'polymorphic native descriptors are not supported yet'
# The ordinary native caller is a test-only consumer, matching the existing
# native_effects target-boundary fixture. It introduces no production ABI axiom.
if [ "${SOMA_TEST_HVF:-0}" = 1 ]; then
 mkdir "$WORK/image"
 cp "$HERE/examples/example_projects/native_abi/fixture.ml" "$HERE/examples/example_projects/native_abi/fixture.definition" "$WORK/image/"
 printf '[project]\nname = "native_abi_image"\nversion = "0.1.0"\n' >"$WORK/image/soma.toml"
 printf '%s\n' 'Require Import Soma.Native.' 'invoke : (unit -> entry nat) -> nat.' >"$WORK/image/caller.definition"
 printf '%s\n' 'let invoke f = f ()' >"$WORK/image/caller.ml"
 cat >"$WORK/image/main.soma" <<'SOMA'
Require Import Sandbox.
Require Import Soma.Native.
Import fixture caller.
Definition native_probe : Native.entry nat := Native.Export
 (Native.Bind (Native.Call_callback fixture.make_item ("old", ("label", fun _ => tt))) (fun original =>
 Native.Bind (Native.Call_callback fixture.set_value (original, "updated")) (fun _ =>
 Native.Bind (Native.Call_callback fixture.copy_value (original, "copy")) (fun copied =>
 Native.Bind (Native.Call_callback fixture.get_value original) (fun old_text =>
 Native.Bind (Native.Call_callback fixture.get_value copied) (fun new_text =>
 Native.Bind (Native.Call_callback fixture.same (original, copied)) (fun same =>
 Native.Bind (Native.Call_callback fixture.join (old_text, new_text)) (fun joined =>
 Native.Return (if andb (negb same) (String.eqb joined "updatedcopy") then 42 else 0))))))))).
Definition main : io unit :=
 value <- call (fun _ => invoke (fun _ => native_probe)) ;;
 if Nat.eqb value 42 then print "native ABI in Solo5 verified" else exit 1.
SOMA
 image_dir=${SOMA_MIRAGE_DIR:-$WORK/image-project}
 if [ -n "${SOMA_NATIVE_IMAGE_TEMPLATE:-}" ]; then
   template_dir="$image_dir/$(basename "$SOMA_NATIVE_IMAGE_TEMPLATE")"
   mkdir -p "$template_dir"
   rsync -a --exclude _build --exclude .git "$SOMA_NATIVE_IMAGE_TEMPLATE/" "$template_dir/"
 fi
 SOMA_MIRAGE_SWITCH=${SOMA_MIRAGE_SWITCH:-kykeon} SOMA_MIRAGE_DIR="$image_dir" \
   "$SOMA" build "$WORK/image/main.soma" >"$WORK/image-build.log" 2>&1 || { cat "$WORK/image-build.log";exit 1; }
 opam exec --switch="${SOMA_MIRAGE_SWITCH:-kykeon}" -- solo5-hvt --mem=256 -- "$WORK/image/main.hvt" >"$WORK/image-boot.log" 2>&1 || { cat "$WORK/image-boot.log";exit 1; }
 rg -q 'native ABI in Solo5 verified' "$WORK/image-boot.log" || { cat "$WORK/image-boot.log";exit 1; }
 printf '%s\n' 'PASS: native record Type/Get/Set/Build/Copy and Callback compile and boot in Solo5'
fi
printf '%s\n' 'PASS: native ABI declaration checks complete'
