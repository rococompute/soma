#!/usr/bin/env bash
# Open native rows preserve width polymorphism without an exhaustive eliminator.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 45 "$work"/*.log 2>/dev/null || true; fi; if [ "${KEEP:-0}" = 1 ]; then echo "Retained $work"; else rm -rf "$work"; fi; exit "$rc"' EXIT
cd "$work"
cat > row.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Type bytes := "Bytes.t".
OCaml Native Open Polymorphic Variant token (Row : Type) :=
 [ "N" : PrimInt63.int; "V" : string; "O" : string; "End"; "Hook" : (string -> bytes) ].
OCaml Native Construct Factory number : forall Row:Type, unit -> PrimInt63.int -> token Row := "N".
OCaml Native Construct Factory variable : forall Row:Type, unit -> string -> token Row := "V".
OCaml Native Construct Factory operator : forall Row:Type, unit -> string -> token Row := "O".
OCaml Native Construct Factory finish : forall Row:Type, unit -> unit -> token Row := "End".
OCaml Native Construct Factory hook : forall Row:Type, unit -> (string -> bytes) -> token Row := "Hook".
OCaml Native Construct direct : forall Row:Type, PrimInt63.int -> token Row := "N".
Fail OCaml Native View exhaustive : forall Row:Type, token Row -> (PrimInt63.int + (string + (string + (unit + (string -> bytes)))))%type.
Fail OCaml Native Open Polymorphic Variant bad (Row : Type; Other : Type) := [ "N" : PrimInt63.int ].
Fail OCaml Native Open Polymorphic Variant recursive (Row : Type) := [ "Again" : Row ].
Fail OCaml Native Open Polymorphic Variant nested_recursive (Row : Type) := [ "Again" : (string -> Row) ].
Fail OCaml Native Open Polymorphic Variant evidence (Row : Prop) := [ "N" : PrimInt63.int ].
Fail OCaml Native Open Polymorphic Variant duplicate (Row : Type) := [ "N"; "N" ].
Fail OCaml Native Construct Factory wrong_payload : forall Row:Type, unit -> string -> token Row := "N".
Fail OCaml Native Construct Factory absent : forall Row:Type, unit -> string -> token Row := "Missing".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
Import row.
Definition number_fn {Row:Type} := Native.Export(Native.Call_callback(number Row)tt).
Definition variable_fn {Row:Type} := Native.Export(Native.Call_callback(variable Row)tt).
Definition operator_fn {Row:Type} := Native.Export(Native.Call_callback(operator Row)tt).
Definition finish_fn {Row:Type} := Native.Export(Native.Call_callback(finish Row)tt).
Definition hook_fn {Row:Type} := Native.Export(Native.Call_callback(hook Row)tt).
Definition direct_fn {Row:Type}(value:PrimInt63.int) := Native.Export(Native.Call_callback(direct Row)value).
Definition main (Row:Type) := (number_fn (Row:=Row), variable_fn (Row:=Row), operator_fn (Row:=Row), finish_fn (Row:=Row), hook_fn (Row:=Row), direct_fn (Row:=Row)).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
rows=list(Path('native').glob('soma_variant_*.ml'))
assert len(rows)==1
text=rows[0].read_text()
assert "type 'row t = ([>"in text and "] as 'row)"in text,text
assert 'native-open-polyvariant'in Path('native/native_abi.manifest').read_text()
PY
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/{prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_variant_*.ml .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let original_number()=(fun n->`N n)
let current_number=Prog.number_fn
let original_variable()=(fun value->`V value)
let current_variable=Prog.variable_fn
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let a=[`Extra 17;Prog.number_fn()31;Prog.variable_fn()"value";Prog.operator_fn()"+";Prog.finish_fn()()]in
 let b=[`Other "tag";Prog.direct_fn 19]in
 require "independent widened row instantiations"(match a,b with [`Extra 17;`N 31;`V "value";`O "+";`End],[`Other "tag";`N 19]->true|_->false);
 let payload=Bytes.to_string(Bytes.make 1048576 's')in
 require "string payload identity"(match Prog.variable_fn()payload with `V value->value==payload|_->false);
 let bytes=Bytes.create 1048576 in let callback _=bytes in
 require "function payload identity"(match Prog.hook_fn()callback with `Hook value->value==callback&&value "ignored"==bytes|_->false);
 require "number constructor sharing"((original_number()==original_number())=(current_number()==current_number()));
 require "string constructor sharing"((original_variable()==original_variable())=(current_variable()==current_variable()));
 let measure fn=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.before in
 let same name old current=let a=measure old and b=measure current in require name(a=b);Printf.printf "%s %.0f/%.0f B\n%!"name a b in
 same "constructor creation"original_number current_number;
 let old=original_number()and current=current_number()in
 same "constructor invocation"(fun()->old(Sys.opaque_identity 31))(fun()->current(Sys.opaque_identity 31));
 let retained factory=let weak=Weak.create 1 in
  let[@inline never] prepare()=let value=Bytes.to_string(Bytes.make 1048576 'w')in Weak.set weak 0(Some value);factory()value in
  let[@inline never] hold()=let variant=prepare()in collect();require "row retains original payload"(Weak.check weak 0);ignore(Sys.opaque_identity variant)in
  hold();collect();not(Weak.check weak 0)in
 require "dropped row releases payload"(retained original_variable&&retained current_variable);
 print_endline "PASS: open native variants preserve independent widened rows, borrowed strings/functions, closed callback phases, exact allocations and Weak lifetimes."
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml soma_variant_*.ml soma_bindings.ml prog.mli prog.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
cp hash.log before-hash
cp row.definition original-row.definition
python3 - <<'PYTHON'
from pathlib import Path
p=Path('row.definition');s=p.read_text().replace('Open Polymorphic Variant token','Polymorphic Variant token',1)
s='\n'.join(line for line in s.splitlines()if not line.startswith('Fail OCaml Native View exhaustive'))+'\n'
p.write_text(s)
PYTHON
soma extract main.soma -no-soma-prelude -o closed >closed.log 2>&1
soma hash main.soma -no-soma-prelude >closed-hash
if cmp -s before-abi closed/native_abi.manifest;then echo 'open row ABI did not change' >&2;exit 1;fi
if cmp -s before-hash closed-hash;then echo 'open row semantic hashes did not change' >&2;exit 1;fi
# A generated typed boundary rejects a primitive returning a non-variant.
cp original-row.definition row.definition
cat > wrong.ml <<'ML'
let number value=value
ML
cat > wrong.definition <<'SOMA'
From Corelib Require Import PrimInt63.
Import row.
OCaml Native External Value wrong : forall Row:Type, PrimInt63.int -> token Row := "Wrong.number".
SOMA
cat > wrong_main.soma <<'SOMA'
From Soma Require Import Native.
Import wrong.
Definition exported {Row:Type} := Native.Export(Native.Call_callback(wrong Row)tt).
Definition main := @exported.
SOMA
soma extract wrong_main.soma -no-soma-prelude -o rejected >wrong-extract.log 2>&1
if (cd rejected && dune build --profile release -j2)>wrong-build.log 2>&1;then echo 'bad primitive ABI was accepted' >&2;exit 1;fi
