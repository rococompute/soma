#!/usr/bin/env bash
# Extract once, build the generated project, call its actual entry points from
# native and bytecode clients. No project-specific runtime or interpreter.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 70 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
cp "$ROOT/examples/example_files/native_effects/native_effects.soma" "$WORK/main.soma"
cd "$WORK"
soma extract main.soma -o native > extract.log 2>&1
soma hash main.soma > hash.log 2>&1
# Signed storage indices use Rocq's existing primitive machine-integer type.
# No additional axiom, evaluator or admitted proposition is permitted.
python3 - <<'PY_AUDIT'
from pathlib import Path
allowed={"Corelib.Numbers.Cyclic.Int63.PrimInt63.int"}
observed=set()
for line in Path("hash.log").read_text().splitlines():
 if "  assumes " in line:observed.update(line.split("  assumes ",1)[1].split())
if observed!=allowed:raise SystemExit("unexpected native library assumptions: "+repr(observed))
PY_AUDIT
test -f native/soma_effect.ml
test -f native/soma_handles.ml
test ! -f native/config.ml
grep -q '(libraries lwt)' native/dune
(cd native && dune build --profile release) > build.log 2>&1
cp native/{prog.ml,prog.mli,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cp "$ROOT/test-suite/misc/soma_native_effects_runtime.ml" check.ml
for compiler in ocamlc ocamlopt; do
  ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
    soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml > "$compiler.log" 2>&1
  "./check-$compiler"
done
# Foreign callers can accept native entry callbacks at their real native type.
mkdir foreign
printf '[project]\nname = "native_entry_signature"\nversion = "0.1.0"\n' > foreign/soma.toml
cat > foreign/caller.definition <<'SOMA'
Require Import Soma.Native.
check : (unit -> entry nat) -> nat.
check_callback : callback unit nat -> nat.
SOMA
printf 'let check f = f ()\nlet check_callback f = f ()\n' > foreign/caller.ml
cat > foreign/main.soma <<'SOMA'
Require Import Soma.Native.
Import caller.
Definition main : entry nat := Export (Invoke
 (fun _ => check (fun _ => Export (Return 42))) (fun value =>
 Bind (New_callback (fun _ _ => Return value)) (fun body => Invoke (fun _ => check_callback body) Return))).
SOMA
(cd foreign && soma extract main.soma -o native && cd native && dune build --profile release) > signature.log 2>&1
printf 'let check (_ : unit -> string) = 0\nlet check_callback f = f ()\n' > foreign/caller.ml
(cd foreign && soma extract main.soma -o native) > bad-signature.log 2>&1
if (cd foreign/native && dune build --profile release) >> bad-signature.log 2>&1; then
 echo 'accepted a foreign callback with the wrong native entry type' >&2; exit 1
fi
grep -q 'Soma_effect.entry\|int\|Soma_nat.nat' bad-signature.log
printf 'let check f = f ()\nlet check_callback (_ : string -> int) = 0\n' > foreign/caller.ml
(cd foreign && soma extract main.soma -o native) > bad-callback-signature.log 2>&1
if (cd foreign/native && dune build --profile release) >> bad-callback-signature.log 2>&1; then
 echo 'accepted a foreign callback with the wrong native callback type' >&2; exit 1
fi
grep -q 'Soma_effect.callback\|string\|unit' bad-callback-signature.log
# A native result cannot be converted back into its original effect program.
cat > inspect.soma <<'SOMA'
Require Import Soma.Native.
Definition inspect (value : entry nat) : program nat :=
 match value with Export body => body end.
Definition main := inspect.
SOMA
if soma extract inspect.soma -o inspected > inspect-extract.log 2>&1; then
  echo 'accepted inspection of a native entry' >&2; exit 1
fi
grep -q 'Native programs and entry points cannot be inspected' inspect-extract.log
cat > inspect_callback.soma <<'SOMA'
Require Import Soma.Native.
Definition inspect (value : callback nat nat) : nat :=
 match value with Callback id => id | Named_callback _ _ => 0 end.
Definition main := inspect.
SOMA
if soma extract inspect_callback.soma -o inspected-callback > inspect-callback.log 2>&1; then
 echo 'accepted inspection of a native callback handle' >&2; exit 1
fi
grep -q 'Native programs and entry points cannot be inspected' inspect-callback.log
# A flat native triple is distinct from nested binary products at the ABI.
mkdir triple
cat > triple/caller.definition <<'SOMA'
Require Import Soma.Native.
OCaml Native Callback check : triple nat string bool -> nat := "check".
SOMA
printf 'let check (value, text, flag) = if text = "payload" && flag then value else 0\n' > triple/caller.ml
cat > triple/main.soma <<'SOMA'
Require Import Soma.Native.
Import caller.
Definition main := Export (Call_callback check (Triple 42 "payload" true)).
SOMA
(cd triple && soma extract main.soma -o native && cd native && dune build --profile release) > triple-signature.log 2>&1
printf 'let check (value, (text, flag)) = if text = "payload" && flag then value else 0\n' > triple/caller.ml
(cd triple && soma extract main.soma -o native) > bad-triple-signature.log 2>&1
if (cd triple/native && dune build --profile release) >> bad-triple-signature.log 2>&1; then
 echo 'accepted a nested pair at the flat native triple boundary' >&2; exit 1
fi
grep -q 'expected of type\|but an expression was expected' bad-triple-signature.log
# Four-component native tuples must stay flat across a real FFI signature.
mkdir quadruple
cat > quadruple/caller.definition <<'SOMA'
From Soma Require Native.
OCaml Native Callback check : Native.quadruple nat unit bool string -> nat := "check".
SOMA
printf 'let check (value, (), flag, text) = if flag && text = "payload" then value else 0\n' > quadruple/caller.ml
cat > quadruple/main.soma <<'SOMA'
From Soma Require Native.
Import caller.
Definition main:=Native.Export(Native.Call_callback check(Native.Quadruple 42 tt true "payload")).
SOMA
(cd quadruple && soma extract main.soma -o native && cd native && dune build --profile release) > quadruple-signature.log 2>&1
printf 'let check (value, ((), (flag, text))) = if flag && text = "payload" then value else 0\n' > quadruple/caller.ml
(cd quadruple && soma extract main.soma -o native) > bad-quadruple-signature.log 2>&1
if (cd quadruple/native && dune build --profile release) >> bad-quadruple-signature.log 2>&1;then
 echo 'accepted a nested tuple at the flat quadruple boundary' >&2;exit 1
fi
grep -q 'Error:' bad-quadruple-signature.log
cat > inspect_vector_custom.soma <<'SOMA'
From Corelib Require Extraction.
From Soma Require Native.
Definition forbidden (value:Native.vector nat):nat:=match value with Native.Vector id size=>size end.
Extract Constant forbidden => "Array.length".
Definition main:=forbidden.
SOMA
if soma extract inspect_vector_custom.soma -o inspected_vector_custom > inspect_vector_custom.log 2>&1;then
 echo 'accepted a consumer vector eliminator with a custom extraction mapping' >&2;exit 1
fi
grep -q 'Native programs and entry points cannot be inspected' inspect_vector_custom.log
# Native storage handles carry their actual Stdlib types across definitions.
mkdir storage
printf '[project]\nname = "native_storage_signature"\nversion = "0.1.0"\n' > storage/soma.toml
cat > storage/caller.definition <<'SOMA'
Require Import Soma.Native.
check : vector string -> text_buffer -> table string string -> PrimInt63.int.
SOMA
cat > storage/caller.ml <<'OCAML'
let check items buffer table =
 Buffer.add_string buffer items.(0);
 Hashtbl.replace table "key" (Buffer.contents buffer);
 Array.length items
OCAML
cat > storage/main.soma <<'SOMA'
Require Import Soma.Native.
Import caller.
Definition main := Export (Bind (Vector_of_list ("payload"::nil)) (fun items =>
 Bind (New_text_buffer 0%uint63) (fun buffer => Bind (New_table 0%uint63) (fun entries =>
 Invoke (fun _ => check items buffer entries) Return)))).
SOMA
(cd storage && soma extract main.soma -o native && cd native && dune build --profile release) > storage-signature.log 2>&1
printf 'let check (_ : string list) (_ : Buffer.t) (_ : (string,string) Hashtbl.t) = 0\n' > storage/caller.ml
(cd storage && soma extract main.soma -o native) > bad-storage-signature.log 2>&1
if (cd storage/native && dune build --profile release) >> bad-storage-signature.log 2>&1; then
 echo 'accepted a list in place of a native vector' >&2; exit 1
fi
grep -q 'vector\|array' bad-storage-signature.log
for handle in vector buffer table; do
 case "$handle" in
  vector) handle_type='vector nat'; handle_pattern='Vector id size' ;;
  buffer) handle_type='text_buffer'; handle_pattern='Text_buffer id' ;;
  table) handle_type='table nat nat'; handle_pattern='Table id' ;;
 esac
 cat > "inspect_${handle}.soma" <<SOMA
Require Import Soma.Native.
Definition main (value : $handle_type) : nat := match value with $handle_pattern => id end.
SOMA
 if soma extract "inspect_${handle}.soma" -o "inspected_${handle}" > "inspect_${handle}.log" 2>&1; then
  echo "accepted inspection of native $handle" >&2; exit 1
 fi
 grep -q 'Native programs and entry points cannot be inspected' "inspect_${handle}.log"
done
# The same generated library boundaries work inside an image, with a native
# caller standing in for Kykeon's current entry-point consumers.
mkdir image
printf '[project]\nname = "native_entry_image"\nversion = "0.1.0"\n' > image/soma.toml
cat > image/caller.definition <<'SOMA'
Require Import Soma.Native.
invoke : (unit -> entry (promise nat)) -> promise nat.
OCaml Native Callback check_triple : triple nat unit bool -> nat := "check_triple".
OCaml Native Callback check_quadruple : quadruple nat unit bool string -> nat := "check_quadruple".
SOMA
printf 'let invoke f = f ()\nlet check_triple (value, (), flag) = if flag then value else 0\nlet check_quadruple (value, (), flag, text) = if flag && text = "quadruple" then value else 0\n' > image/caller.ml
cat > image/main.soma <<'SOMA'
Require Import Sandbox.
Require Import Soma.Native.
From Corelib Require Import PrimInt63.
Import caller.
Definition borrowed_pair {A:Type} (owner:string)(pending:promise A) :=
 Native.Promise_bind_borrowed owner (fun _=>pending)(fun value=>Native.Export(Native.Promise_return value)).
Definition saturated_check (value:nat) : Native.program nat :=
 Native.Bind (Native.Pure_callback (fun value:nat=>value)) (fun unary =>
 Native.Bind (Native.Call_callback unary value) (fun value =>
 Native.Bind (Native.Pure_callback2 (fun (value:nat) (_:unit)=>value)) (fun binary =>
 Native.Bind (Native.Call_callback2 binary value tt) (fun value =>
 Native.Bind (Native.New_callback2 (fun _ a b1 => Native.Return a)) (fun callback =>
 Native.Bind (Native.Call_callback2 callback value tt) (fun value =>
 Native.Bind (Native.New_callback3 (fun _ a b1 b2 => Native.Return a)) (fun callback =>
 Native.Bind (Native.Call_callback3 callback value tt tt) (fun value =>
 Native.Bind (Native.New_callback4 (fun _ a b1 b2 b3 => Native.Return a)) (fun callback =>
 Native.Bind (Native.Call_callback4 callback value tt tt tt) (fun value =>
 Native.Bind (Native.New_callback5 (fun _ a b1 b2 b3 b4 => Native.Return a)) (fun callback =>
 Native.Bind (Native.Call_callback5 callback value tt tt tt tt) (fun value =>
 Native.Bind (Native.New_callback6 (fun _ a b1 b2 b3 b4 b5 => Native.Return a)) (fun callback =>
 Native.Bind (Native.Call_callback6 callback value tt tt tt tt tt) (fun value =>
 Native.Return value)))))))))))))).
Definition curried_check (value : nat) : Native.program nat :=
 Native.Bind (Native.New_callback2 (fun _ a b => Native.Return (a, b))) (fun pair =>
 Native.Bind (Native.Call_callback pair value) (fun second =>
 Native.Bind (Native.Call_callback second tt) (fun pair =>
 Native.Bind (Native.New_callback6 (fun _ (a : nat) (b : unit) (c : bool) (d e f : unit) =>
   Native.Bind (Native.Call_callback check_triple (Native.Triple a b c)) (fun checked =>
   Native.Call_callback check_quadruple (Native.Quadruple checked b c "quadruple")))) (fun callback =>
 Native.Bind (Native.Call_callback callback (fst pair)) (fun next =>
 Native.Bind (Native.Call_callback next (snd pair)) (fun next =>
 Native.Bind (Native.Call_callback next true) (fun next =>
 Native.Bind (Native.Call_callback next tt) (fun next =>
 Native.Bind (Native.Call_callback next tt) (fun next =>
 Native.Call_callback next tt))))))))).
Definition paired_check (original copied : string) : Native.program (promise nat) :=
 Native.Bind (Native.Promise_return (if String.eqb original copied then 42 else 0)) (fun left =>
 Native.Bind (Native.Promise_return tt) (fun right =>
 Native.Bind Native.Promise_unit (fun unit_pending =>
 Native.Bind (@Native.Promise_none unit) (fun none_pending =>
 Native.Bind (Native.Int64_of_int 200000000%uint63) (fun duration =>
 Native.Bind (Native.Promise_settled unit_pending) (fun ready =>
 Native.Bind (Native.Promise_pick (left::nil)) (fun winner =>
 Native.Bind (Native.Bind (Native.Promise_both winner right) (borrowed_pair original)) (fun combined =>
 Native.Promise_map_borrowed original (fun _ => combined) (fun result => Native.Export (
 Native.Protect (Native.Raise_failure "native image failure") (fun _ =>
 Native.Protect (Native.Assert_failure "native image assertion" 7 9) (fun _ =>
 Native.Bind (curried_check (fst result)) saturated_check)))))))))))).
Definition native_probe : Native.entry (promise nat) := Native.Export
 (Native.Bind (Native.Vector_of_list ("payload"::nil)) (fun items =>
 Native.Bind (Native.New_callback (fun _ value => Native.Return value)) (fun mapper =>
 Native.Bind (Native.Bind (Native.Bind (Native.List_map mapper ("payload"::nil)) (fun _=>Native.Vector_map mapper items)) (fun mapped =>
  if andb (Nat.eqb (Native.vector_size mapped) 1) (PrimInt63.eqb (Native.vector_word_size mapped) 1%uint63)
  then Native.Return mapped else Native.Raise_failure "readonly size mismatch")) (fun mapped_items =>
 Native.Bind (Native.New_text_buffer 0%uint63) (fun buffer =>
 Native.Bind (Native.Text_buffer_append buffer "payload") (fun _ =>
 Native.Bind (Native.Text_buffer_contents buffer) (fun text =>
 Native.Bind (Native.New_table 0%uint63) (fun entries =>
 Native.Bind (Native.Table_replace entries "key" text) (fun _ =>
 Native.Bind (Native.Table_find entries "key") (fun copied =>
 Native.Bind (Native.Vector_get mapped_items 0%uint63) (fun original =>
 Native.loop_then (fun remaining => Native.Return (match remaining with
   0 => Native.Finish tt | S next => Native.Continue next end)) 3
   (fun _ => paired_check original copied)))))))))))).
Definition native_tail_probe : Native.entry(promise nat) := Native.Export
 (Native.tail_invoke(fun _=>invoke(fun _=>native_probe))).
Definition main : io unit :=
 pending <- call (fun _ => invoke (fun _ => native_tail_probe)) ;;
 value <- await_promise pending ;;
 if Nat.eqb value 42 then print "native library boundary in Solo5 verified" else exit 1.
SOMA
(cd image && SOMA_MIRAGE_DIR="$WORK/image-project" soma build --no-image main.soma) > image-check.log 2>&1
if [ "${SOMA_TEST_HVF:-0}" = 1 ]; then
 (cd image && SOMA_MIRAGE_DIR="$WORK/image-project" soma build main.soma) > image-build.log 2>&1
 timeout 20 opam exec --switch="${SOMA_MIRAGE_SWITCH:-hvf}" -- solo5-hvt --mem=256 -- image/main.hvt > image-boot.log 2>&1
 grep -q 'native library boundary in Solo5 verified' image-boot.log
fi
echo 'native library effects: ok'
