#!/usr/bin/env bash
# Public type equations come from checked Source and MiniML, never ML parsing.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 35 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String.
Inductive json(A:Type) := Null | Bool(value:bool) | Num(value:A)
 | Str(value:string) | Arr(values:list(json A)) | Obj(fields:list(string*json A)).
Record entry := Entry {path:string;mode:PrimInt63.int;data:string}.
Record box(A:Type) := Box {payload:A;ordinal:PrimInt63.int}.
Inductive branch(A:Type) := Branch(children:list(twig A))
with twig(A:Type) := Twig(parent:option(branch A)).
Definition copy_branch{A}(value:branch A) := value.
Definition copy_twig{A}(value:twig A) := value.
Definition items(A:Type) := list A.
Definition external(A:Type) := option A.
Definition copy_json{A}(value:json A) := value.
Definition entry_path(value:entry) := path value.
Definition copy_box{A}(value:box A) := value.
Definition copy_items{A}(value:items A) := value.
Definition copy_external{A}(value:external A) := value.
Definition unused := bool.
Definition main := (@copy_json,(entry_path,(@copy_box,(@copy_items,(@copy_external,(@copy_branch,@copy_twig)))))).
Fail OCaml Native Public Types copy_json With [Type "value" := json].
Fail OCaml Native Public Types main With [Type "value" := copy_json].
Fail OCaml Native Public Types main With [Type "unused" := unused].
Fail OCaml Native Public Types main With [Type "value" := json;Type "value" := box].
Fail OCaml Native Public Types main With [Type "value;bad" := json].
Fail OCaml Native Public Types main With [Value "value" := copy_json].
OCaml Native Public Types main With [Type "json_value" := json;Type "entry" := entry;
 Type "box_value" := box;Type "list_value" := items;Type "option_value" := external;
 Type "branch_value" := branch;Type "twig_value" := twig].
Fail OCaml Native Public Types main With [Type "again" := json].
Fail OCaml Native Assembly main As "duplicate".
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
rows=Path('native/native_assemblies.manifest').read_text().splitlines()
assert rows[0]=='soma-native-assemblies-v1' and len(rows)==3
for line in rows[1:]:
 symbol,source,src_hash,name,digest,program,interface,bindings,layout,contract=shlex.split(line)
 for path,expected in [(source,src_hash),('native/'+name,digest),('native/prog.ml',program),('native/prog.mli',interface),('native/soma_bindings.ml',bindings)]:
  assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==expected,path
 assert next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]==symbol)==contract
 abi=[shlex.split(l)for l in Path('native/native_abi.manifest').read_text().splitlines()[1:]]
 identity=next(i for s,_,h,i in abi if s==symbol and h==src_hash).replace('\\n','\n')
 assert 'public-type-equations-v1' in identity
 assert hashlib.sha256(identity.encode()).hexdigest()==layout
for line in Path('hash.log').read_text().splitlines():
 assumptions=set(line.split('  assumes ',1)[1].split(', '))if'  assumes 'in line else set()
 assert assumptions<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},assumptions
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_bindings.ml} .
cp native/main.assembly public.ml
cp native/main.assembly-interface public.mli
cat >check.ml <<'ML'
module P=Public
let require name condition=if not condition then failwith name
let ()=
 let integers:int P.json_value=P.Arr[P.Num 3;P.Obj["key",P.Bool true]]in
 let strings:string P.json_value=P.Obj["key",P.Str "value"]in
 require "recursive integer alias" (P.copy_json integers==integers);
 require "recursive string alias" (P.copy_json strings==strings);
 let branches:int P.branch_value=P.Branch[P.Twig None]in
 let twigs:string P.twig_value=P.Twig(Some(P.Branch[]))in
 require "mutual type equations" (P.copy_branch branches==branches && P.copy_twig twigs==twigs);
 let record:P.entry={P.path="abc";mode=511;data="payload"}in
 require "record labels and nominal equation" (P.entry_path record="abc");
 let integer_box:int P.box_value={P.payload=19;ordinal=7}in
 let string_box:string P.box_value={P.payload="text";ordinal=8}in
 require "generic record identity" (P.copy_box integer_box==integer_box && P.copy_box string_box==string_box);
 let ints:int P.list_value=[3;7]and texts:string P.list_value=["x";"y"]in
 require "type alias genericity" (P.copy_items ints==ints && P.copy_items texts==texts);
 let some:int P.option_value=Some 3 and text:string P.option_value=Some "a"in
 require "keyword type and name allocation" (P.copy_external some==some && P.copy_external text==text);
 Gc.full_major();
 let before=Gc.allocated_bytes()in
 for _=1 to 10000 do ignore(P.copy_box integer_box);ignore(P.copy_json strings)done;
 let consumed=Gc.allocated_bytes()-.before in
 let before=Gc.allocated_bytes()in
 for _=1 to 10000 do ignore integer_box;ignore strings done;
 let baseline=Gc.allocated_bytes()-.before in
 require "equations introduce no call allocation" (consumed=baseline);
 print_endline "PASS: checked record labels, recursive constructors, generic aliases, physical identity and zero extra allocation"
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt.unix -linkpkg -w -a uint63.ml soma_nat.ml soma_word64.ml soma_handles.ml soma_effect.ml float64.ml soma_bindings.ml public.mli public.ml check.ml -o check >"$compiler.log" 2>&1
 ./check
done
# Type equations can supplement checked public partial applications.
python3 - <<'PY_MIX'
from pathlib import Path
source=Path('main.soma').read_text().split('Fail OCaml Native Public Types copy_json',1)[0]
source=source.replace('Definition main :=', 'Definition apply_id (prefix:string) (value:PrimInt63.int) := value.\nDefinition prepared := EmptyString.\nDefinition main :=',1)
start=source.index('Definition main :=');source=source[:start]+"Definition main := (@copy_json,(entry_path,(apply_id,prepared))).\n"
Path('mixed.soma').write_text(source+'''OCaml Native Public Assembly main With [Apply "run" := apply_id With [prepared]].
OCaml Native Public Types main With [Type "json_value" := json;Type "entry" := entry].
''')
# Failures at extraction must be explicit; never publish a guessed type shape.
base=Path('main.soma').read_text().split('Fail OCaml Native Public Types copy_json',1)[0]
Path('collision.soma').write_text(base+'OCaml Native Public Types main With [Type "json" := box].\n')
Path('indexed.soma').write_text('''From Soma Require Import Native OCaml.
Inductive indexed(n:nat) := Index(value:bool).
Definition keep(n:nat)(value:indexed n) := value.
Definition main := keep.
Fail OCaml Native Public Types main With [Type "indexed_public" := indexed].
''')
Path('opaque.soma').write_text("From Soma Require Import Native OCaml.\nDefinition marker := true.\n")
Path('opaque.exp').write_text('''Lemma hidden : Type.
Proof. exact bool. Qed.
Definition keep(value:hidden) := value.
Definition main := keep.
Fail OCaml Native Public Types main With [Type "hidden_public" := hidden].
''')
PY_MIX
soma hash indexed.soma -no-soma-prelude >indexed.log 2>&1
soma hash opaque.soma -no-soma-prelude >opaque.log 2>&1
if soma extract collision.soma -no-soma-prelude -o collision >collision.log 2>&1;then
 echo 'public type shadow was accepted';exit 1
fi
grep -q 'shadow an extracted type' collision.log
test ! -e collision/collision.assembly
soma extract mixed.soma -no-soma-prelude -o mixed-native >mixed.log 2>&1
cp mixed-native/mixed.assembly mixed.ml
cp mixed-native/mixed.assembly-interface mixed.mli
cat >check_mixed.ml <<'ML'
let ()=
 let value:int Mixed.json_value=Mixed.Num 17 in
 assert(Mixed.copy_json value==value);
 let entry:Mixed.entry={Mixed.path="a";mode=7;data="b"}in
 assert(Mixed.entry_path entry="a");assert(Mixed.run 32=32);
 print_endline "PASS: public type equations compose with checked partial applications"
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt.unix -linkpkg -w -a uint63.ml soma_nat.ml soma_word64.ml soma_handles.ml soma_effect.ml float64.ml soma_bindings.ml mixed.mli mixed.ml check_mixed.ml -o mixed-check >"$compiler-mixed.log" 2>&1
 ./mixed-check
done
# Renaming only the public type changes the checked owner's semantic identity.
cp hash.log before.log
sed -i.bak 's/"json_value"/"json_public"/' main.soma
soma hash main.soma -no-soma-prelude >after.log
python3 - <<'PY'
from pathlib import Path
def main(file):return next(l.split()[0]for l in Path(file).read_text().splitlines()if l.split()[2]=='main.main')
assert main('before.log')!=main('after.log')
PY
# Removing the producer cleans both complete implementation/interface products.
# Use a clean ordinary Source client for producer-switch cleanup.
cat >main.soma <<'SOMA'
Definition main := true.
SOMA
soma extract main.soma -no-soma-prelude -o native >plain.log 2>&1
test ! -e native/main.assembly
test ! -e native/main.assembly-interface
test ! -e native/native_assemblies.manifest
printf 'PASS: authenticated type products, semantic fingerprints and stale producer cleanup\n'
