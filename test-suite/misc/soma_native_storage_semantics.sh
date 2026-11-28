#!/usr/bin/env bash
# Check the logical word model against actual extracted storage entry points.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >main.soma <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String Strings.Ascii.
Definition make_vector {A} (items:list A) := Native.Export (Native.Vector_of_list items).
Definition get_vector {A} (items:Native.vector A) index := Native.Export (Native.Vector_get items index).
Definition set_vector {A} (items:Native.vector A) index value := Native.Export (Native.Vector_set items index value).
Definition vector_size {A} (items:Native.vector A) := Native.Export (Native.Vector_length items).
Definition snapshot {A} (items:Native.vector A) := Native.Export (Native.Vector_to_list items).
Definition make_buffer capacity := Native.Export (Native.New_text_buffer capacity).
Definition append buffer text := Native.Export (Native.Text_buffer_append buffer text).
Definition add_char buffer character := Native.Export (Native.Text_buffer_char buffer character).
Definition contents buffer := Native.Export (Native.Text_buffer_contents buffer).
Definition missing (_:unit) : Native.entry unit := Native.Export Native.Raise_not_found.
Definition fail message : Native.entry unit := Native.Export (Native.Raise_failure message).
Definition main := (@make_vector, @get_vector, @set_vector, @vector_size, @snapshot,
 make_buffer, append, add_char, contents, missing, fail).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,prog.ml,prog.mli} .
cat >check.ml <<'ML'
let error f = try f (); failwith "expected bounds error" with Invalid_argument message as e ->
 assert(message="index out of bounds");e
let () =
 assert(Sys.word_size=64 && Sys.int_size=63);
 assert(Sys.max_array_length=18014398509481983 && Sys.max_floatarray_length=Sys.max_array_length);
 assert(Sys.max_string_length=144115188075855863);
 let output=open_out Sys.argv.(1) in
 Printf.fprintf output "profile\t%d\t%d\t%d\n" Sys.word_size Sys.max_array_length Sys.max_string_length;
 let indices=[min_int;min_int+1;-100;-2;-1;0;1;2;3;4;5;6;7;8;9;10;max_int-1;max_int] in
 for length=0 to 8 do
  List.iter(fun index ->
   let vector=Prog.make_vector(List.init length Fun.id) in
   let observed=try Some(Prog.get_vector vector index) with Invalid_argument message ->
    assert(message="index out of bounds");None in
   let expected=if index>=0 && index<length then Some index else None in
   assert(observed=expected && Prog.vector_size vector=length);
   Printf.fprintf output "%d\t%d\t%s\n" length index
    (match observed with Some value->string_of_int value|None->"none");
   let before=Prog.snapshot vector in
   (match observed with
    | Some position -> Prog.set_vector vector index 77;
      assert(Prog.snapshot vector=List.mapi(fun i value->if i=position then 77 else value)before)
    | None -> ignore(error(fun()->Prog.set_vector vector index 77));assert(Prog.snapshot vector=before));
   assert(Prog.vector_size vector=length)
  )indices
 done;
 close_out output;
 let first=Bytes.make 8 'a' and second=Bytes.make 8 'b' in
 let vector=Prog.make_vector[first;second] in
 assert(Prog.get_vector vector 0==first && List.nth(Prog.snapshot vector)1==second);
 Prog.set_vector vector 1 first;assert(Prog.get_vector vector 1==first);
 let empty1=Prog.make_vector [] and empty2=Prog.make_vector [] in assert(empty1==empty2);
 let ex1=error(fun()->ignore(Prog.get_vector vector (-1))) in
 let ex2=error(fun()->ignore(Prog.get_vector vector (-1))) in assert((ex1==ex2)=(Sys.backend_type=Sys.Native));
 let missing ()=try Prog.missing ();failwith "missing exception" with Not_found as e->e in
 assert(missing()==missing());
 List.iter(fun capacity ->
  let buffer=Prog.make_buffer capacity in assert(Prog.contents buffer="");
  Prog.append buffer "a\000\255";let snapshot=Prog.contents buffer in
  let alias=buffer in Prog.add_char alias '\128';
  assert(snapshot="a\000\255" && Prog.contents buffer="a\000\255\128");
  Prog.append alias "tail";assert(Prog.contents buffer="a\000\255\128tail")
 )[min_int;-8;-1;0;1;64];
 let failure ()=try Prog.fail "payload";failwith "missing failure" with Failure "payload" as e->e in
 assert(failure()!=failure());
 print_endline "PASS: actual storage entries, signed bounds, canonical empty arrays, readonly length, generic aliases, byte buffers and exception identity"
ML
for backend in ocamlopt ocamlc; do
 ocamlfind "$backend" -w -a -package lwt -linkpkg soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml -o "check-$backend" >"$backend.log" 2>&1
 "./check-$backend" "observed-$backend.tsv"
done
cmp observed-ocamlopt.tsv observed-ocamlc.tsv
# The runtime observations become Gallina obligations, not OCaml generation.
# Kernel computation checks the model at every observed signed index, including
# max_int/min_int, without constructing huge unary naturals for rejected indices.
python3 - <<'PY'
from pathlib import Path
rows=Path('observed-ocamlopt.tsv').read_text().splitlines()
_,word,arrays,strings=rows[0].split('\t');assert word=='64'
proof=['From Corelib Require Import PrimInt63.',
       'From Soma Require Import NativeWord.',
       'From Stdlib Require Import ZArith.',
       f'Example runtime_limits : array_limit = {arrays}%Z /\\ string_limit = {strings}%Z.',
       'Proof. vm_compute. split; reflexivity. Qed.']
for number,row in enumerate(rows[1:]):
 count,index,value=row.split('\t');bits=int(index)%(1<<63)
 result='None' if value=='none' else f'Some {value}'
 proof += [f'Example observed_{number} : bounded_index {bits}%uint63 {count} = {result}.',
           'Proof. vm_compute. reflexivity. Qed.']
Path('observed.v').write_text('\n'.join(proof)+'\n')
print(f'Checking {len(rows)-1} signed-index observations against the kernel word model')
PY
rocq c -q -no-soma-prelude observed.v >model.log 2>&1
echo 'PASS: native and bytecode storage observations agree with the logical 64-bit word model'
