#!/usr/bin/env bash
# Logical owned tables against the actual extracted default Hashtbl operations.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
export TABLE_SOURCE="$root/theories/Soma/NativeTable.v"
export TABLE_SPEC_SOURCE="$root/theories/Soma/NativeTableSpec.v"
export TABLE_ASSUMPTIONS="$root/test-suite/misc/soma_native_table.assumptions.json"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
python3 - <<'PYTHON'
from pathlib import Path
import json, os, re, subprocess
expected = json.loads(Path(os.environ['TABLE_ASSUMPTIONS']).read_text())
names = {module + '.' + name for module, variable in
         [('NativeTable','TABLE_SOURCE'),('NativeTableSpec','TABLE_SPEC_SOURCE')]
         for name in re.findall(r'^(?:Theorem|Lemma) (\w+)', Path(os.environ[variable]).read_text(), re.M)}
assert names == set(expected), (names - set(expected), set(expected) - names)
for number, name in enumerate(sorted(names)):
    file = Path(f'assumptions_{number}.v')
    file.write_text(f'Require Import Soma.{name.split(".")[0]}.\nPrint Assumptions {name}.\n')
    result = subprocess.run(['rocq','c','-q','-no-soma-prelude',str(file)],
                            capture_output=True,text=True)
    assert result.returncode == 0, result.stdout + result.stderr
    actual = set(re.findall(r"^([A-Za-z_][\w.\x27]*)\s*:",result.stdout,re.M)) - {'Axioms'}
    assert actual == set(expected[name]), (name,actual,expected[name],result.stdout)
print(f'PASS: {len(names)} table theorem inventories match the exact existing primitive/law assumptions',flush=True)
PYTHON
cat >main.soma <<'SOMA'
From Soma Require Import Native NativeTable.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String.
Definition new_word {V:Type} capacity := Native.Export (@Native.New_table PrimInt63.int V capacity).
Definition new_text {V:Type} capacity := Native.Export (@Native.New_table string V capacity).
Definition word_mem {V:Type} (table:Native.table PrimInt63.int V) key := Native.Export (Native.Table_mem table key).
Definition text_mem {V:Type} (table:Native.table string V) key := Native.Export (Native.Table_mem table key).
Definition word_find {V:Type} (table:Native.table PrimInt63.int V) key := Native.Export (Native.Table_find table key).
Definition text_find {V:Type} (table:Native.table string V) key := Native.Export (Native.Table_find table key).
Definition word_opt {V:Type} (table:Native.table PrimInt63.int V) key := Native.Export (Native.Table_find_opt table key).
Definition text_opt {V:Type} (table:Native.table string V) key := Native.Export (Native.Table_find_opt table key).
Definition word_set {V:Type} (table:Native.table PrimInt63.int V) key value := Native.Export (Native.Table_replace table key value).
Definition text_set {V:Type} (table:Native.table string V) key value := Native.Export (Native.Table_replace table key value).
Definition word_remove {V:Type} (table:Native.table PrimInt63.int V) key := Native.Export (Native.Table_remove table key).
Definition text_remove {V:Type} (table:Native.table string V) key := Native.Export (Native.Table_remove table key).
Definition word_model {V:Type} := @NativeTable.lookup PrimInt63.int V Word_keys.
Definition text_model {V:Type} := @NativeTable.lookup string V String_keys.
Definition word_replace {V:Type} := @NativeTable.replace PrimInt63.int V Word_keys.
Definition text_replace {V:Type} := @NativeTable.replace string V String_keys.
Definition word_drop {V:Type} := @NativeTable.remove PrimInt63.int V Word_keys.
Definition text_drop {V:Type} := @NativeTable.remove string V String_keys.
Definition main := (@new_word,@new_text,@word_mem,@text_mem,@word_find,@text_find,
 @word_opt,@text_opt,@word_set,@text_set,@word_remove,@text_remove,
 @word_model,@text_model,@word_replace,@text_replace,@word_drop,@text_drop).
Verification Properties "word_replacement_readback" Invariants "other_word_keys_preserved" Trust "Corelib.Numbers.Cyclic.Int63.PrimInt63.int; Corelib.Numbers.Cyclic.Int63.Uint63Axioms.eqb_correct; Corelib.Numbers.Cyclic.Int63.Uint63Axioms.eqb_refl".
SOMA
cat >main.exp <<'PROOFS'
Theorem word_replacement_readback : forall V key (value:V) entries,
 word_model key (word_replace key value entries) = Some value.
Proof. intros. apply NativeTable.lookup_replaced. Qed.
Theorem other_word_keys_preserved : forall V key other (value:V) entries,
 key <> other -> word_model other (word_replace key value entries) = word_model other entries.
Proof. intros. apply NativeTable.lookup_replaced_other. assumption. Qed.
PROOFS
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,prog.ml,prog.mli} .
cat >check.ml <<'ML'
let checked=ref 0
let equal actual expected=incr checked;if actual<>expected then failwith "table observation differs from Source model"
let not_found f=try ignore(f());failwith "expected Not_found" with Not_found as error->error
let collect()=Gc.full_major();Gc.full_major()
let ()=
 assert(Sys.int_size=63);
 List.iter(fun capacity->
  let first=Prog.new_word capacity and second=Prog.new_word capacity in
  assert(first!=second);equal(Prog.word_mem first 0)false;
  equal(Prog.word_opt first min_int)None;
  assert(not_found(fun()->Prog.word_find first 0)==Not_found);
  let text=Prog.new_text capacity in equal(Prog.text_mem text "")false;
  assert(not_found(fun()->Prog.text_find text "")==Not_found)
 )[min_int;-16;-1;0;1;16;128];
 let random=Random.State.make[|17;63;20261128|]in
 let run()=
  let words=Prog.new_word 8 and texts=Prog.new_text 8 in
  let wm=ref[]and tm=ref[]in
  let keys=[|min_int;min_int+1;-4096;-1;0;1;4096;max_int-1;max_int|]in
  let names=[|"";"a";"long key";"a\000b";"\000";"\255\128";"same";String.make 4096 'k'|]in
  for i=0 to 9999 do
   let key=keys.(Random.State.int random(Array.length keys))in
   let name=names.(Random.State.int random(Array.length names))in
   (match Random.State.int random 4 with
    |0->Prog.word_remove words key;wm:=Prog.word_drop key !wm;
        Prog.text_remove texts name;tm:=Prog.text_drop name !tm
    |1->(* Borrowed tables may already have duplicate bindings from Hashtbl.add. *)
        Hashtbl.add words key i;wm:=(key,i)::!wm;
        Hashtbl.add texts name i;tm:=(name,i)::!tm
    |_->Prog.word_set words key i;wm:=Prog.word_replace key i !wm;
        Prog.text_set texts name i;tm:=Prog.text_replace name i !tm);
   equal(Prog.word_opt words key)(Prog.word_model key !wm);
   equal(Prog.text_opt texts name)(Prog.text_model name !tm);
   equal(Prog.word_mem words key)(Prog.word_model key !wm<>None);
   equal(Prog.text_mem texts name)(Prog.text_model name !tm<>None);
   let wk=keys.(Random.State.int random(Array.length keys))in
   let tk=names.(Random.State.int random(Array.length names))in
   equal(Prog.word_opt words wk)(Prog.word_model wk !wm);
   equal(Prog.text_opt texts tk)(Prog.text_model tk !tm)
  done
 in
 run();Hashtbl.randomize();run();
 let borrowed=Bytes.make 128 'v'in
 let words=Prog.new_word 0 in Prog.word_set words 0 borrowed;
 assert(Prog.word_find words 0==borrowed&&Prog.word_model 0[0,borrowed]=Some borrowed);
 Bytes.set borrowed 0 'x';assert(Bytes.get(Prog.word_find words 0)0='x');
 let fault=Failure "table callback"in let body flag=if flag then borrowed else raise fault in
 let functions=Prog.new_text 0 in Prog.text_set functions "body" body;
 assert(Prog.text_find functions "body"==body&&(Prog.text_find functions "body")true==borrowed);
 (try ignore((Prog.text_find functions "body")false);assert false with error->assert(error==fault));
 let keys=Prog.new_text 0 and old_key=Weak.create 1 and new_key=Weak.create 1 in
 let[@inline never] populate()=
  let old=Bytes.to_string(Bytes.make 32768 'q')and incoming=Bytes.to_string(Bytes.make 32768 'q')in
  Weak.set old_key 0(Some old);Weak.set new_key 0(Some incoming);
  Hashtbl.add keys old borrowed;Prog.text_set keys incoming borrowed;
  let actual,_=List.hd(List.of_seq(Hashtbl.to_seq keys))in assert(actual==incoming)
 in
 populate();collect();assert(not(Weak.check old_key 0)&&Weak.check new_key 0);
 let[@inline never] remove()=match Weak.get new_key 0 with
  |Some key->Prog.text_remove keys key|None->assert false in
 remove();collect();assert(not(Weak.check new_key 0));
 (* The logical string carrier is immutable. An unsafe bytes alias can break
    native bucket reachability and therefore needs a separate representation law. *)
 let bytes=Bytes.of_string "unsafe key"in let key=Bytes.unsafe_to_string bytes in
 let table=Hashtbl.create ~random:false 16 in Hashtbl.add table key 7;
 let old=Hashtbl.hash key land 15 in
 let rec change n=if n=256 then assert false else
  (Bytes.set bytes 0(Char.chr n);if Hashtbl.hash key land 15=old then change(n+1))in
 change 0;
 assert(Prog.text_opt table key=None&&Prog.text_model key[key,7]=Some 7);
 Printf.printf "PASS: %d word/string table observations, duplicate removal, random seeds, generic aliases/faults and natural key lifetimes; unsafe-key boundary exposed\n%!"!checked
ML
for backend in ocamlopt ocamlc; do
 ocamlfind "$backend" -w -a -package lwt -linkpkg soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml -o "check-$backend" >"$backend.log" 2>&1
 "./check-$backend"
done
cat >model.v <<'COQ'
From Soma Require Import Native NativeTable NativeSemantics NativeTableSpec NativeTotal.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String.
Import ListNotations.
Definition no_foreign A (_:unit->A) (_:world) (_:NativeSemantics.result A) (_:world) := False.
Definition no_named A B (_ _:string) (_:A) (_:world) (_:NativeSemantics.result B) (_:world) := False.
Example duplicate_word_key : NativeTable.lookup Word_keys 1%uint63
  (NativeTable.remove Word_keys 1%uint63 [(1%uint63,3);(1%uint63,2)]) = Some 2.
Proof. vm_compute. reflexivity. Qed.
Example duplicate_string_key : NativeTable.lookup String_keys "x"%string
  (NativeTable.remove String_keys "x"%string [("x"%string,3);("x"%string,2)]) = Some 2.
Proof. vm_compute. reflexivity. Qed.
Example negative_capacity_is_total : NativeTotal.total no_foreign no_named (fun _ _=>True)
  (empty_world,@Native.New_table PrimInt63.int nat (PrimInt63.sub 0%uint63 1%uint63)).
Proof. apply (@new_table_is_total no_foreign no_named PrimInt63.int nat empty_world
  (PrimInt63.sub 0%uint63 1%uint63) Word_keys). Qed.
Example unsupported_unit_keys_stay_unsupported post :
 ~ NativeTotal.total no_foreign no_named post (empty_world,@Native.New_table unit unit 0%uint63).
Proof. apply unsupported_table_is_not_total. Qed.
Fail Definition mismatched_domain : key_domain (unit->unit) := Word_keys.
COQ
rocq c -q -no-soma-prelude model.v >model.log 2>&1
echo 'PASS: kernel-checked duplicate lookup, supported progress and unsupported-key non-totality'
python3 - <<'PYTHON'
from pathlib import Path
import os, re, subprocess, tomllib
receipt=tomllib.loads(Path('native/verification.toml').read_text())
expected={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int',
          'Corelib.Numbers.Cyclic.Int63.Uint63Axioms.eqb_refl',
          'Corelib.Numbers.Cyclic.Int63.Uint63Axioms.eqb_correct'}
assert set(receipt['used-assumptions']) == expected, receipt
assert {row['name'] for row in receipt['invariants']} == {'other_word_keys_preserved'}
source=Path('main.soma');original=source.read_text()
law='Corelib.Numbers.Cyclic.Int63.Uint63Axioms.eqb_correct; '
assert original.count(law)==1
source.write_text(original.replace(law,''))
result=subprocess.run(['soma','extract','main.soma','-no-soma-prelude','-o','rejected'],
                      capture_output=True,text=True)
assert result.returncode!=0 and 'eqb_correct' in result.stdout+result.stderr, result.stdout+result.stderr
source.write_text(original)
print('PASS: Source verification records existing equality laws and rejects omission before publication',flush=True)
source=Path(os.environ['TABLE_SOURCE']).read_text()
def change(before,after):
    assert source.count(before)==1,before
    return source.replace(before,after)
cases=[('baseline',source,None),
       ('old_value',change('then (key,value)::rest','then (key,before)::rest'),'lookup_replaced'),
       ('lost_old_duplicates',change('then rest\n    else (stored,value)::remove',
                                    'then remove domain key rest\n    else (stored,value)::remove'),
                                    'remove_first_duplicate'),
       ('miss_drops_existing',change('else (stored,value)::remove domain key rest',
                                    'else remove domain key rest'),'lookup_removed_other')]
for name,text,theorem in cases:
    file=Path('mutation_'+name+'.v');file.write_text(text)
    result=subprocess.run(['rocq','c','-q','-no-soma-prelude',str(file)],capture_output=True,text=True)
    if theorem is None:
        assert result.returncode==0,result.stdout+result.stderr
        continue
    assert result.returncode!=0,name+': changed implementation passed'
    begin=text.index('Theorem '+theorem)
    first=text[:begin].count('\n')+1
    last=text[:text.index('Qed.',begin)].count('\n')+1
    assert any(first<=int(line)<=last for line in re.findall(r'line (\d+),',result.stdout+result.stderr)),result.stdout+result.stderr
    print('PASS: '+theorem+' rejects '+name,flush=True)
PYTHON
