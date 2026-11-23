#!/usr/bin/env bash
# Closed native polymorphic variants: real generated code and typed boundaries.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 45 "$WORK"/*.log 2>/dev/null || true; fi; rm -rf "$WORK"' EXIT
ocaml() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }
mkdir "$WORK/app"
cp "$HERE"/examples/example_projects/native_variants/* "$WORK/app/"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
python3 - "$WORK/native" "$WORK/app" "$WORK/hash" <<'PY'
import pathlib,sys,hashlib,shlex
out,app=map(pathlib.Path,sys.argv[1:3]);seen=set()
for line in pathlib.Path(sys.argv[3]).read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split())
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
assert not(out/'protocol.ml').exists()
rows=[shlex.split(s)for s in(out/'native_variants.manifest').read_text().splitlines()[1:]]
assert (out/'native_variants.manifest').read_text().startswith('soma-native-variants-v1\n')
mods={}
for symbol,source,source_hash,filename,generated_hash in rows:
 assert hashlib.sha256((app/source).read_bytes()).hexdigest()==source_hash
 assert hashlib.sha256((out/filename).read_bytes()).hexdigest()==generated_hash
 assert 'Obj.'not in(out/filename).read_text()
 mods[symbol]=filename[:-3][0].upper()+filename[:-3][1:]
assert len(mods)==4 and len(set(mods.values()))==4
assert mods['protocol.A__B.item']!=mods['protocol.A.B.item']
assert 'native-owned-polyvariant'in(out/'native_abi.manifest').read_text()
(out/'probe.ml').write_text('module Reply='+mods['protocol.reply']+'\nmodule Owned='+mods['protocol.owned']+'\n')
print('PASS: no added assumptions, distinct schema namespaces and exact source/generated provenance')
PY
cat >> "$WORK/native/probe.ml" <<'ML'
let require label condition=if not condition then failwith label
let raw_view=function `Data x->Ok x|`Eof->Error(Ok())|`Error x->Error(Error x)
let raw_owned=function `Borrowed x->Ok x|`Callback f->Error(Ok f)|`Unit x->Error(Error(Ok x))|`Empty->Error(Error(Error()))
let physical_shape left right=
 let a=Obj.repr left and b=Obj.repr right in
 Obj.is_int a=Obj.is_int b && if Obj.is_int a then a=b else
 Obj.tag a=Obj.tag b && Obj.size a=Obj.size b && Obj.field a 0=Obj.field b 0 && Obj.field a 1==Obj.field b 1
let ()=
 let text=Bytes.to_string(Bytes.of_string"payload")in
 let generated:Reply.t=Prog.make_data text in
 let raw:[`Data of string|`Eof|`Error of string]=`Data text in
 require"exact Data native layout"(physical_shape raw generated);
 require"Data borrowed payload"(match Prog.reply_view generated with Ok x->x==text|_->false);
 require"Error exact native layout"(physical_shape(`Error text)(Prog.make_error text));
 require"Eof immediate tag"(physical_shape `Eof(Prog.make_eof()));
 List.iter(fun value->require"frozen native dispatch"(Prog.reply_view value=raw_view value);
  require"Source classifier"(Prog.classify(Prog.reply_view value)=match value with `Data _->1|`Eof->2|`Error _->3))
  [raw;`Eof;`Error text];
 Bytes.set(Bytes.unsafe_of_string text)0 'P';
 require"unsafe native string mutation alias"(match Prog.reply_view generated with Ok x->x==text&&x.[0]='P'|_->false);
 let error_tag=Obj.field(Obj.repr(`Error text))0 in
 Obj.set_field(Obj.repr generated)0 error_tag;
 require"live valid-tag mutation"(Prog.reply_view generated=raw_view generated&&
  match Prog.reply_view generated with Error(Error x)->x==text|_->false);

 let node=Borrowed.make_node"borrowed"in
 let wrapped=Prog.make_borrowed node in
 require"borrowed native object layout"(physical_shape(`Borrowed node)wrapped);
 require"borrowed native object identity"(match Prog.owned_view wrapped with Ok x->x==node|_->false);
 let key=Lwt.new_key()in let pending,wake=Lwt.task()in
 let callback()=require"callback context"(Lwt.get key=Some 73);pending in
 let wrapped=Prog.make_callback callback in
 require"callback native layout"(physical_shape(`Callback callback)wrapped);
 let found=match Prog.owned_view wrapped with Error(Ok f)->f|_->failwith"callback branch"in
 require"callback physical identity"(found==callback);
 let result=Lwt.with_value key(Some 73)found in require"returned promise identity"(result==pending);
 Lwt.wakeup wake();require"promise completion"(Lwt.state result=Lwt.Return());
 require"nullary vs unit payload layout"(physical_shape `Empty(Prog.make_empty())&&physical_shape(`Unit())(Prog.make_unit())&&
  Obj.is_int(Obj.repr(Prog.make_empty()))&&not(Obj.is_int(Obj.repr(Prog.make_unit()))));
 List.iter(fun value->require"frozen owned dispatch"(Prog.owned_view value=raw_owned value))
  [`Borrowed node;`Unit();`Empty];
 require"nested namespace one"(Prog.namespace_one(`Value text)==text);
 require"nested namespace two"(Prog.namespace_two(`Value true));
 print_endline"PASS: frozen native tag/header/payload layouts, nullary/unit distinction, borrowed mutable aliases, callback/promise identity and dynamic scope"
let weak value=let w=Weak.create 1 in Weak.set w 0(Some value);w
let[@inline never] weak_probe view make=
 let text=Bytes.to_string(Bytes.make 2048 'x')in
 let parent=make text in let wp=weak parent and wt=weak text in
 let selected=view parent in
 Gc.full_major();let states=Weak.check wp 0,Weak.check wt 0 in
 ignore(Sys.opaque_identity selected);states
let ()=
 require"original view owner/payload Weak phases"(weak_probe raw_view(fun x->`Data x)=weak_probe Prog.reply_view Prog.make_data);
 let marker=Bytes.create 2048 in let w=weak marker in
 let callback()=ignore(Sys.opaque_identity marker);Lwt.return_unit in
 let value=Prog.make_callback callback in
 Gc.full_major();require"stored callback provider alive"(Weak.check w 0);
 let f=match Prog.owned_view value with Error(Ok f)->f|_->failwith"callback"in
 require"stored callback identity"(f==callback);
 print_endline"PASS: native view payload/parent Weak phases match the frozen matcher and stored callback ownership is retained"
let[@inline never] raw_during value observe=observe(raw_view value)
let[@inline never] during_probe invoke ()=
 let holder=ref(Weak.create 0)in
 let observe _=Gc.full_major();Weak.check !holder 0 in
 let[@inline never] tail()=
  let value=`Data(Bytes.to_string(Bytes.create 2048))in holder:=weak value;invoke value observe in
 tail()
let ()=
 let raw=during_probe raw_during()and generated=during_probe Prog.view_during()in
 Printf.printf "view callback parent Weak: raw=%b generated=%b\n"raw generated;
 require"parent root released before downstream callback"(raw=generated)

ML
python3 - "$WORK/native" <<'PY'
from pathlib import Path
import sys
out=Path(sys.argv[1]);mods=sorted(p.stem for p in out.glob('*.ml')if p.stem!='soma_main')
(out/'dune').write_text('(executable (name probe) (modes exe byte) (modules '+' '.join(mods)+') (libraries lwt) (flags (:standard -w -a)))\n')
PY
(cd "$WORK/native" && ocaml dune build --profile release probe.exe probe.bc) > "$WORK/build.log" 2>&1
"$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"
# Type-valued schema dependencies must select Borrowed even without a view.
printf '%s\n' 'From Soma Require Native.' 'Import protocol.' 'Definition main:=Native.Export(Native.Call_callback empty_value tt).' > "$WORK/app/carrier.soma"
"$SOMA" extract "$WORK/app/carrier.soma" -o "$WORK/carrier" > "$WORK/carrier.log" 2>&1
test -f "$WORK/carrier/borrowed.ml"
(cd "$WORK/carrier" && ocaml dune build --profile release) > "$WORK/carrier-build.log" 2>&1
# Reordering equally typed cases changes interpretation without changing the
# native structural type. Both program identity and generated receipts change.
python3 - "$WORK/app/protocol.definition" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);p.write_text(p.read_text().replace('"Data" : string; "Eof"; "Error" : string','"Error" : string; "Eof"; "Data" : string'))
PY
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/changed-hash"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/changed" > "$WORK/changed.log" 2>&1
python3 - "$WORK" <<'PY'
from pathlib import Path
import sys,shlex
w=Path(sys.argv[1]);digest=lambda p:next(l.split()[0]for l in p.read_text().splitlines()if l.split()[2]=='main.main')
assert digest(w/'hash')!=digest(w/'changed-hash')
rows=lambda p:{r[0]:r for r in[shlex.split(s)for s in(p/'native_variants.manifest').read_text().splitlines()[1:]]}
a,b=rows(w/'native')['protocol.reply'],rows(w/'changed')['protocol.reply']
assert a[3]==b[3]and a[2]!=b[2]and a[4]!=b[4]
print('PASS: case interpretation/order invalidates program hashes and source/generated provenance with stable module identity')
PY
# Invalid schemas/descriptors fail at Soma's typed declaration boundary.
negative() {
 local name=$1 text=$2 expected=$3
 mkdir "$WORK/$name"
 printf 'From Soma Require Native.\n%s\n' "$text" > "$WORK/$name/bad.definition"
 printf 'Import bad.\nDefinition main:=tt.\n' > "$WORK/$name/main.soma"
 if "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/out" > "$WORK/$name.log" 2>&1; then echo "accepted $name" >&2; exit 1; fi
 grep -q "$expected" "$WORK/$name.log"
}
negative collision 'OCaml Native Polymorphic Variant t:=["TlQjwsvudQY";"TSwizMiGxdn"].' 'tag hash collision'
negative duplicate 'OCaml Native Polymorphic Variant t:=["A";"A"].' 'tags must be distinct'
negative injected 'OCaml Native Polymorphic Variant t:=["A; bad"].' 'must be an OCaml identifier'
negative wrongview 'OCaml Native Polymorphic Variant t:=["A":string;"B"]. OCaml Native View bad:t->string.' 'ordered nested result'
negative wrongpayload 'OCaml Native Polymorphic Variant t:=["A":string]. OCaml Native Construct bad:bool->t:="A".' 'argument differs'
negative nullary 'OCaml Native Polymorphic Variant t:=["A"]. OCaml Native Construct bad:string->t:="A".' 'argument differs'
negative unknowntag 'OCaml Native Polymorphic Variant t:=["A"]. OCaml Native Construct bad:unit->t:="B".' 'tag is absent'
negative polymorphic 'OCaml Native Polymorphic Variant t:=["A":forall A:Type,A->A].' 'must be monomorphic'
negative recordview 'OCaml Native Record t:={value:string}. OCaml Native View bad:t->string.' 'declared native polymorphic variant'
negative variantget 'OCaml Native Polymorphic Variant t:=["A"]. OCaml Native Get bad:t->string:="value".' 'declared native type'
# Opaque handles have no logical native tag inspector.
mkdir "$WORK/inspection"
cp "$HERE"/examples/example_projects/native_variants/{protocol.definition,borrowed.definition,borrowed.ml} "$WORK/inspection/"
printf '%s\n' 'From Soma Require Native.' 'Import protocol.' 'Definition main(value:reply):nat:=match value with Native.Native_handle id=>id end.' > "$WORK/inspection/main.soma"
if "$SOMA" extract "$WORK/inspection/main.soma" -o "$WORK/inspection/out" > "$WORK/inspection.log" 2>&1; then echo 'accepted native variant inspection' >&2;exit 1;fi
grep -q 'cannot be inspected' "$WORK/inspection.log"
echo 'PASS: malformed/schema/type/descriptor and opaque-inspection negatives'
# A companion's raw native signature must accept the actual closed row type.
mkdir "$WORK/ffi"
cp "$HERE"/examples/example_projects/native_variants/{protocol.definition,borrowed.definition,borrowed.ml} "$WORK/ffi/"
cat > "$WORK/ffi/caller.definition" <<'SOMA'
From Soma Require Native.
Import protocol.
OCaml Native Callback consume : reply -> nat := "consume".
SOMA
printf 'let consume = function `Data _ -> 42 | `Eof -> 0 | `Error _ -> 1\n' > "$WORK/ffi/caller.ml"
cat > "$WORK/ffi/main.soma" <<'SOMA'
From Soma Require Native.
Import protocol caller.
Definition main:=Native.Export(Native.Bind(Native.Call_callback data "payload")(fun value=>Native.Call_callback consume value)).
SOMA
"$SOMA" extract "$WORK/ffi/main.soma" -o "$WORK/ffi/native" > "$WORK/ffi.log" 2>&1
(cd "$WORK/ffi/native" && ocaml dune build --profile release) >> "$WORK/ffi.log" 2>&1
printf 'let consume (_ : [ `Data of bool | `Eof | `Error of string ]) = 42\n' > "$WORK/ffi/caller.ml"
"$SOMA" extract "$WORK/ffi/main.soma" -o "$WORK/ffi/bad" > "$WORK/ffi-negative.log" 2>&1
if (cd "$WORK/ffi/bad" && ocaml dune build --profile release) >> "$WORK/ffi-negative.log" 2>&1; then echo 'accepted wrong native variant payload' >&2;exit 1;fi
grep -q 'bool\|string' "$WORK/ffi-negative.log"
echo 'PASS: actual closed-row FFI signature and wrong-native-payload compile rejection'
# Distinct library binding names compose without changing checked semantics.
SOMA_OCAML_BINDINGS_MODULE=Network_bindings "$SOMA" extract "$WORK/app/main.soma" -o "$WORK/namespaced" > "$WORK/namespaced.log" 2>&1
test -f "$WORK/namespaced/network_bindings.ml"
test ! -f "$WORK/namespaced/soma_bindings.ml"
(cd "$WORK/namespaced" && ocaml dune build --profile release) >> "$WORK/namespaced.log" 2>&1
SOMA_OCAML_BINDINGS_MODULE=Network_bindings "$SOMA" hash "$WORK/app/main.soma" > "$WORK/namespaced-hash"
cmp "$WORK/changed-hash" "$WORK/namespaced-hash"
for module_name in 'Bad.Name' 'bad' 'Prog' 'Soma_effect' 'Protocol'; do
 if SOMA_OCAML_BINDINGS_MODULE="$module_name" "$SOMA" extract "$WORK/app/main.soma" -o "$WORK/namespace-bad" > "$WORK/namespace-bad.log" 2>&1; then echo 'accepted invalid/colliding binding module' >&2;exit 1;fi
 grep -q 'module identifier\|collides' "$WORK/namespace-bad.log"
done
echo 'PASS: namespaced native libraries compile with unchanged logical hashes; invalid/colliding names are rejected'

if [ "${SOMA_TEST_HVF:-0}" = 1 ];then
 mkdir "$WORK/image"
 cp "$HERE"/examples/example_projects/native_variants/{protocol.definition,borrowed.definition,borrowed.ml} "$WORK/image/"
 printf '[project]\nname="native_variant_image"\nversion="0.1.0"\n' > "$WORK/image/soma.toml"
 printf 'From Soma Require Native.\ninvoke : (unit -> Native.entry nat) -> nat.\n' > "$WORK/image/caller.definition"
 printf 'let invoke f = f ()\n' > "$WORK/image/caller.ml"
 cat > "$WORK/image/main.soma" <<'SOMA'
Require Import Sandbox.
From Soma Require Native.
Import protocol caller.
Definition probe:=Native.Export(Native.Bind(Native.Call_callback data "borrowed")(fun value=>
 Native.Bind(Native.Call_callback view_reply value)(fun reply=>
 match reply with Native.Ok text=>
   Native.Bind(Native.Call_callback eof tt)(fun value=>
   Native.Bind(Native.Call_callback view_reply value)(fun ended=>
    match ended with Native.Error(Native.Ok _)=>
     Native.Protect(Native.Raise_invalid_argument "native variant image")
      (fun _=>Native.Return(if String.eqb text "borrowed"then 42 else 0))
    |_=>Native.Return 0 end))
 |_=>Native.Return 0 end))).
Definition main:io unit:=
 value<-call(fun _=>invoke(fun _=>probe));;
 if Nat.eqb value 42 then print "native polymorphic variants in Solo5 verified"else exit 1.
SOMA
 SOMA_MIRAGE_SWITCH=${SOMA_MIRAGE_SWITCH:-kykeon} SOMA_MIRAGE_DIR="$WORK/image-project" \
 SOMA_OCAML_BINDINGS_MODULE=Image_bindings "$SOMA" build "$WORK/image/main.soma" > "$WORK/image-build.log" 2>&1
 timeout 30 opam exec --switch="${SOMA_MIRAGE_SWITCH:-kykeon}" -- solo5-hvt --mem=256 -- "$WORK/image/main.hvt" > "$WORK/image-boot.log" 2>&1
 grep -q 'native polymorphic variants in Solo5 verified' "$WORK/image-boot.log"
 echo 'PASS: native variant construction/view and invalid_argument execute inside actual Solo5'
fi
echo 'native variant schemas: ok'
