#!/usr/bin/env bash
# Whole checked declarations retain their receiving unit's native constants.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 20 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >main.soma <<'SOMA'
From Stdlib Require Import List Bool Strings.String Strings.Ascii.
From Soma Require Import OCaml.
Import ListNotations.
Local Open Scope string_scope.
Definition catalog := ["alpha";"beta";"alpha";"a""b";"a\b"].
Definition empty (A:Type):list A := [].
Definition data := ((Some "alpha",[true;false]),tt).
Definition character := "q"%char.
Definition unused := ["unused"].
Definition main := (catalog,(@empty,(data,character))).
SOMA
cat >main.exp <<'SOMA'
Theorem catalog_length : List.length catalog=5.
Proof. reflexivity. Qed.
SOMA
soma extract main.soma -no-soma-prelude -o baseline >baseline.log 2>&1
soma hash main.soma -no-soma-prelude >baseline-hash.log
cat >>main.soma <<'SOMA'
Fail OCaml Native Literal Declaration catalog From catalog.
Fail OCaml Native Literal Declaration main From main.
Fail OCaml Native Literal Declaration main From unused.
OCaml Native Literal Declaration main From catalog.
OCaml Native Literal Declaration main From empty.
OCaml Native Literal Declaration main From data.
OCaml Native Literal Declaration main From character.
Fail OCaml Native Literal Declaration main From catalog.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
for suffix in ['.ml','.mli']:assert Path('baseline/prog'+suffix).read_bytes()==Path('native/prog'+suffix).read_bytes()
def hashes(path):return {l.split()[2]:l.split()[:2]for l in Path(path).read_text().splitlines()}
old,new=hashes('baseline-hash.log'),hashes('hash.log')
assert old['main.catalog_length']==new['main.catalog_length']
assert old['main.catalog']==new['main.catalog'] and old['main.main']!=new['main.main']
lines=Path('native/native_literal_declarations.manifest').read_text().splitlines();assert lines[0]=='soma-native-literal-declarations-v1'and len(lines)==5
abis=[shlex.split(l)for l in Path('native/native_abi.manifest').read_text().splitlines()[1:]]
artifacts=[]
for row in lines[1:]:
 owner,source,src,symbol,name,filename,decl,sig,ml,mli,identity,contract=shlex.split(row)
 assert(owner,source,symbol)==('main.main','main.soma','main.'+name)
 assert contract==new[owner][0]
 for path,h in [(source,src),('native/'+filename,decl),('native/'+filename+'-interface',sig),('native/prog.ml',ml),('native/prog.mli',mli)]:
  assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==h
 assert any(o==owner and h==src and hashlib.sha256(i.replace('\\n','\n').encode()).hexdigest()==identity for o,_,h,i in abis)
 artifacts.append((name,filename))
Path('artifacts').write_text('\n'.join(name+' '+filename for name,filename in artifacts)+'\n')
prefix='let marker="alpha"\n'
suffix='let get()=catalog\nlet last="alpha"\n'
Path('after.ml').write_text(prefix+''.join(Path('native',filename).read_text()for _,filename in artifacts)+suffix)
Path('after.mli').write_text('val marker:string\n'+''.join(Path('native',filename+'-interface').read_text()for _,filename in artifacts)+'val get:unit -> string list\nval last:string\n')
PY
# This independent compiler-AST oracle selects entire original declarations;
# it never reconstructs a production binding or its expression.
cat >oracle.ml <<'ML'
let parse path=let c=open_in path in Fun.protect ~finally:(fun()->close_in c)(fun()->Parse.implementation(Lexing.from_channel c))
let read p=let c=open_in p in Fun.protect ~finally:(fun()->close_in c)(fun()->really_input_string c(in_channel_length c))
let ()=
 let program=parse "baseline/prog.ml"in
 let channel=open_in "artifacts"in
 let selected=ref[]in
 (try while true do let line=input_line channel in let space=String.index line ' 'in
  let name=String.sub line 0 space and file=String.sub line(space+1)(String.length line-space-1)in
  let declaration=List.find(fun item->match item.Parsetree.pstr_desc with
   |Pstr_value(_, [{pvb_pat={ppat_desc=Ppat_var id;_};_}])->id.txt=name|_->false)program in
  assert(Format.asprintf "%a" Pprintast.structure[declaration]=Format.asprintf "%a" Pprintast.structure(parse("native/"^file)));
  selected:= !selected@[declaration]
 done with End_of_file->close_in channel);
 let c=open_out "before.ml"in output_string c("let marker=\"alpha\"\n"^Format.asprintf "%a" Pprintast.structure !selected^"\nlet get()=catalog\nlet last=\"alpha\"\n");close_out c;
 let c=open_out "before.mli"in output_string c(read "after.mli");close_out c;
 assert(Format.asprintf "%a" Pprintast.structure(parse "before.ml")=Format.asprintf "%a" Pprintast.structure(parse "after.ml"));
 print_endline "PASS complete original program bytes unchanged and each whole literal declaration/receiving-unit AST identical"
ML
ocamlfind ocamlc -package compiler-libs.common -linkpkg oracle.ml -o oracle >oracle.log 2>&1
./oracle
python3 - <<'PY'
from pathlib import Path
for side in ['before','after']:Path(side+'_build.ml').write_text('module Make()=struct\n'+Path(side+'.ml').read_text()+'\nend\n')
PY
cat >check.ml <<'ML'
module A(X:module type of Before)=struct end
module B(X:module type of After)=struct end
module AB=A(After)
module BA=B(Before)
let[@inline never] allocated f=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 1000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.start
let ()=
 assert(Before.catalog=After.catalog&&After.catalog=["alpha";"beta";"alpha";"a\"b";"a\\b"]);
 assert(Before.data=After.data&&After.character='q');
 let i:int list=After.empty and s:string list=After.empty in assert(i=[]&&s=[]);
 assert(Before.get()==Before.catalog&&After.get()==After.catalog);
 let relations values marker last=let first=List.hd values and repeated=List.nth values 2 in first==marker,first==last,first==repeated in
 assert(relations Before.catalog Before.marker Before.last=relations After.catalog After.marker After.last);
 let before=allocated(fun()->let module M=Before_build.Make()in M.catalog)in
 let after=allocated(fun()->let module M=After_build.Make()in M.catalog)in assert(before=after);
 assert(allocated Before.get=allocated After.get);
 let lifetime make=let weak=Weak.create 1 in
  let[@inline never] retain()=let value=make()in Weak.set weak 0(Some value);Gc.full_major();assert(Weak.check weak 0);ignore(Sys.opaque_identity value)in
  retain();Gc.full_major();Weak.check weak 0 in
 let[@inline never] old()=let module M=Before_build.Make()in M.catalog in
 let[@inline never] fresh()=let module M=After_build.Make()in M.catalog in
 assert(lifetime old=lifetime fresh);
 Printf.printf "literal declarations: complete APIs, unrestricted empty list, same-unit strings/static lists, exact factory %.0f/call allocation and natural Weak phases passed\n%!"after
ML
for backend in ocamlopt ocamlc;do
 rm -f ./*.cm[iox] ./*.o
 ocamlfind "$backend" -w -a before.mli before.ml after.mli after.ml before_build.ml after_build.ml check.ml -o check
 ./check
done
cp main.soma original
# Functions and runtime/global dependencies cannot masquerade as constants.
cat >bad.soma <<'SOMA'
From Stdlib Require Import List Strings.String.
From Soma Require Import OCaml.
Import ListNotations.
Definition function_value (x:bool):=if x then [true]else[false].
Definition shared:=[true].
Definition alias:=shared.
Definition main:=(function_value,alias).
OCaml Native Literal Declaration main From function_value.
SOMA
if soma extract bad.soma -no-soma-prelude -o bad-native >bad.log 2>&1;then echo 'accepted a function as a literal declaration' >&2;exit 1;fi
rg -q 'closed native constant' bad.log
sed 's/From function_value\./From alias./' bad.soma >alias.soma
if soma extract alias.soma -no-soma-prelude -o alias-native >alias.log 2>&1;then echo 'accepted a global alias as a literal declaration' >&2;exit 1;fi
rg -q 'closed native constant' alias.log
cat >nominal.soma <<'SOMA'
From Stdlib Require Import List.
From Soma Require Import OCaml.
Import ListNotations.
Inductive token:=Token.
Definition value:list token:=[].
Definition main:=value.
OCaml Native Literal Declaration main From value.
SOMA
if soma extract nominal.soma -no-soma-prelude -o nominal-native >nominal.log 2>&1;then echo 'accepted an undeclared nominal signature dependency' >&2;exit 1;fi
rg -q 'self-contained native' nominal.log
cat >custom.soma <<'SOMA'
From Soma Require Import OCaml.
From Corelib Require Extraction.
Extract Inductive bool => "bool" ["true" "true"].
Definition value:=false.
Definition main:=value.
OCaml Native Literal Declaration main From value.
SOMA
# Soma installs its canonical mappings after importing Source. The attempted
# override therefore does not reach the printer; verify the actual constant
# remains false rather than mistaking this normalization for a rejection.
soma extract custom.soma -no-soma-prelude -o custom-native >custom.log 2>&1
python3 - <<'PY'
from pathlib import Path
import re,shlex
row=shlex.split(Path('custom-native/native_literal_declarations.manifest').read_text().splitlines()[1])
assert re.fullmatch('let '+re.escape(row[4])+r' =\s+false\n',Path('custom-native',row[5]).read_text())
PY
cat >proxy.soma <<'SOMA'
Import main.
Definition main:=main.catalog.
SOMA
soma extract proxy.soma -no-soma-prelude -o proxy-native >proxy.log 2>&1
test ! -f proxy-native/native_literal_declarations.manifest
sed '/OCaml Native Literal Declaration/d' original >main.soma
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
test ! -f native/native_literal_declarations.manifest
test -z "$(find native -name '*.declaration*' -print)"
