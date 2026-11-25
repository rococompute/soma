#!/usr/bin/env bash
# Exact native module equations retain nominal types and all native members.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 40 "$work"/{extract,build}.log 2>/dev/null || true; fi; if [ "${KEEP:-0}" = 1 ]; then echo "Retained $work"; else rm -rf "$work"; fi; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
let initialized=ref 0
let functor_calls=ref 0
module type CORE=sig
 type t
 val make:int->t
 val value:t->int
 val identity:'a->'a
 val slot:t option ref
 exception Fault of t
 module Inner:sig type nonrec t=t val read:t->int end
 val context:string Lwt.key
 val pending:unit->t Lwt.t
 val set_pending:t Lwt.t->unit
end
module MakeCore():CORE=struct
 let()=incr initialized
 type t={value:int}
 let make value={value}
 let value item=item.value
 let identity item=item
 let slot=ref None
 exception Fault of t
 module Inner=struct type nonrec t=t let read=value end
 let context=Lwt.new_key()
 let promise=ref(Lwt.return(make 0))
 let pending()=if Lwt.get context<>Some "caller"then failwith "context";!promise
 let set_pending value=promise:=value
end
module Core=MakeCore()
module Other=MakeCore()
module Make(X:sig val value:int end)=struct
 let()=incr functor_calls
 type t=Token of int
 let make()=Token X.value
end
module New()=struct type t=Fresh end
let marker=()
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native External Value marker : unit := "Target.marker".
SOMA
cat > aliases.definition <<'SOMA'
From Soma Require Import Native.
Module Header.
OCaml Native Module Alias Z := "Target.Core".
OCaml Native Module Alias A := "Z.Inner".
OCaml Native Module Alias Factory := "Target.Make".
OCaml Native Module Alias Generative := "Target.New".
End Header.
Module Footer.
OCaml Native Module Alias Z := "Target.Other".
End Footer.
Fail OCaml Native Module Alias bad := "Target.Core".
Fail OCaml Native Module Alias Bad := "Target.lowercase".
Fail OCaml Native Module Alias Bad := "Target..Core".
Fail OCaml Native Module Alias Bad := "Target.Core; let escaped = true".
Fail OCaml Native Module Alias Bad := "Target.Make(Arg)".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target aliases.
Definition selected := (Header.Z,(Header.A,(Header.Factory,(Header.Generative,Footer.Z)))).
Definition main := (selected,Native.Export(Native.Call_callback marker tt)).
SOMA
cat > main.exp <<'SOMA'
Theorem aliases_have_canonical_bodies : Header.Z = tt /\ Footer.Z = tt.
Proof. split; reflexivity. Qed.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={"Corelib.Numbers.Cyclic.Int63.PrimInt63.int"},seen
assert all("  assumes "not in line for line in Path("hash.log").read_text().splitlines()if " aliases."in line)
lines=Path('native/native_module_aliases.manifest').read_text().splitlines()
assert lines[0]=='soma-native-module-aliases-v1'
rows=[shlex.split(line)for line in lines[1:]];assert len(rows)==5
scopes={}
for symbol,namespace,source,source_hash,filename,digest,name,target,order in rows:
 assert hashlib.sha256(Path(source).read_bytes()).hexdigest()==source_hash
 assert Path(filename).name==filename and filename.endswith('.exports')
 data=Path('native',filename).read_bytes();assert hashlib.sha256(data).hexdigest()==digest
 scopes.setdefault(namespace,[]).append((int(order),name,target,filename))
assert sorted(scopes)==['aliases.Footer','aliases.Header'],scopes
assert [item[1]for item in scopes['aliases.Header']]==['Z','A','Factory','Generative']
assert [item[0]for item in scopes['aliases.Header']]==list(range(4))
Path('names.ml').write_text(''.join('module '+namespace.rsplit('.',1)[1]+' = Soma_bindings.'+Path(items[0][3]).stem.capitalize()+'\n'for namespace,items in sorted(scopes.items())))
for namespace,items in scopes.items():
 Path('raw_'+namespace.rsplit('.',1)[1].lower()+'.ml').write_bytes(Path('native',items[0][3]).read_bytes())
assert 'module Z = Target.Core\nmodule A = Z.Inner\n'in Path('raw_header.ml').read_text()
abi=Path('native/native_abi.manifest').read_text();assert 'native-module-alias'in abi
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_bindings.mli,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
module H=Names.Header
module F=Names.Footer
let ()=require "module aliases do not initialize targets again"(!Target.initialized=2&& !Target.functor_calls=0)
let node=Target.Core.make 31
let read(value:H.Z.t)=Target.Core.value value
let nested(value:H.A.t)=H.Z.value value
let raw(value:Raw_header.Z.t)=H.Z.value value
module Arg=struct let value=37 end
module FromAlias=H.Factory(Arg)
module FromTarget=Target.Make(Arg)
let functor_type(value:FromAlias.t):FromTarget.t=value
let ()=
 require "abstract and nested type equations"(read node=31&&nested node=31&&raw node=31);
 require "exact native function identities"(H.Z.make==Target.Core.make&&H.Z.identity==Target.Core.identity&&H.A.read==Target.Core.Inner.read);
 require "same names in separate namespaces remain distinct"(Obj.repr H.Z.slot!=Obj.repr F.Z.slot&&F.Z.slot==Target.Other.slot);
 H.Z.slot:=Some node;require "same mutable reference and borrowed handle"(H.Z.slot==Target.Core.slot&&match !Target.Core.slot with Some value->value==node|None->false);
 require "exact exception constructor"(try raise(H.Z.Fault node)with Target.Core.Fault value->value==node);
 let bytes=Bytes.make 4096 'b'in require "generic bytes identity"(H.Z.identity bytes==bytes);
 let callback()=bytes in require "generic closure identity"(H.Z.identity callback==callback);
 let promise,_=Lwt.task()in H.Z.set_pending promise;
 Lwt.with_value Target.Core.context(Some "caller")(fun()->require "exact borrowed pending promise/caller context"(H.Z.pending()==promise));
 Lwt.cancel promise;require "cancellation"(match Lwt.state promise with Lwt.Fail Lwt.Canceled->true|_->false);
 require "functor application preserves nominal equality"(match functor_type(FromAlias.make())with FromTarget.Token 37->true|_->false);
 require "only actual functor applications run initialization"(!Target.functor_calls=2);
 let old_module=(module Target.Core:Target.CORE)and current_module=(module H.Z:Target.CORE)in
 require "first-class packaging retains module identity"(old_module==current_module);
 let measure fn=Gc.full_major();let start=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.start in
 let a=measure(fun()->Target.Core.identity node)and b=measure(fun()->H.Z.identity node)in
 require "exact alias call allocation"(a=b);
 Printf.printf "PASS: native module aliases preserve declaration order, scoped names, abstract/nested types, functor applicativity/generativity, native members/state/exceptions, initialization, generic/promise/context/cancellation identities and exact allocation %.0f/%.0f B.\n%!"a b
ML
cat > bad_generativity.ml <<'ML'
module A=Names.Header.Generative()
module B=Target.New()
let impossible(value:A.t):B.t=value
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_bindings.mli soma_bindings.ml prog.mli prog.ml names.ml raw_header.ml raw_footer.ml check.ml
 ./"check-$compiler"
 if ocamlfind "$compiler" -package lwt -c bad_generativity.ml >bad-generativity.log 2>&1;then echo 'alias erased generative type separation' >&2;exit 1;fi
done
cp aliases.definition before-definition
cp native/native_abi.manifest before-abi
cp hash.log before-hash
sed -i.bak 's/Alias Z := "Target.Core"/Alias Z := "Target.Other"/' aliases.definition
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash
if cmp -s before-abi changed/native_abi.manifest;then echo 'alias target ABI unchanged' >&2;exit 1;fi
if cmp -s before-hash changed-hash;then echo 'alias target semantic hash unchanged' >&2;exit 1;fi
python3 - <<'PY'
from pathlib import Path
import re
before=Path('before-hash').read_text();after=Path('changed-hash').read_text()
# The public unit-valued driver must depend on native namespace ownership too.
rows=lambda text:[line for line in text.splitlines()if len(line.split())>=3 and line.split()[2]=='main.main']
a,b=rows(before),rows(after);assert a and b and a!=b,(a,b)
PY
cp before-definition aliases.definition
sed -i.bak 's/"Target.Core"/"Target.Missing"/' aliases.definition
soma extract main.soma -no-soma-prelude -o missing >missing.log 2>&1
if (cd missing && dune build --profile release -j2)>missing-build.log 2>&1;then echo 'missing native module accepted' >&2;exit 1;fi
