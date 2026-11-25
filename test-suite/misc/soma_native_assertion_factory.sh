#!/usr/bin/env bash
# Closed failure factories preserve native/bytecode closure phases and locations.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 50 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat > sites.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native Assertion Factory word_site : unit -> unit -> PrimInt63.int := 42 29.
OCaml Native Assertion Factory bool_site : unit -> unit -> bool := 43 7.
OCaml Native Assertion Factory text_site : unit -> unit -> string := 44 11.
OCaml Native Assertion Factory pending_site : unit -> unit -> promise PrimInt63.int := 45 3.
OCaml Native Assertion Factory polymorphic_site : forall (A : Type), unit -> unit -> A := 46 0.
Fail OCaml Native Assertion Factory missing_factory : unit -> PrimInt63.int := 42 29.
Fail OCaml Native Assertion Factory missing_thunk : PrimInt63.int := 42 29.
Fail OCaml Native Assertion Factory argument : unit -> PrimInt63.int -> PrimInt63.int := 42 29.
Fail OCaml Native Assertion Factory first_argument : PrimInt63.int -> unit -> PrimInt63.int := 42 29.
Fail OCaml Native Assertion Factory labelled : forall (arg : unit), unit -> PrimInt63.int := 42 29.
Fail OCaml Native Assertion Factory zero_line : unit -> unit -> bool := 0 0.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
Import sites.
Definition factory := Native.Export (Native.Call_callback word_site tt).
Definition boolean := Native.Export (Native.Call_callback bool_site tt).
Definition text := Native.Export (Native.Call_callback text_site tt).
Definition pending := Native.Export (Native.Call_callback pending_site tt).
Definition polymorphic := Native.Export (Native.Call_callback (polymorphic_site PrimInt63.int) tt).
Definition main := (factory,boolean,text,pending,polymorphic).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes ' in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
bindings=Path('native/soma_bindings.ml').read_text()
assert 'fun () -> fun () -> Stdlib.raise (Stdlib.Assert_failure (__FILE__, 42, 29))' in bindings
PY
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/{soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
# Embed unmodified compiler output in one unit. Directives give the old/new
# native sites the same original unit filename, as a project renderer can.
{
 printf '# 1 "assertion-fixture.ml"\nmodule Soma_bindings = struct\n'
 cat native/soma_bindings.ml
 printf '\nend\n'
 cat native/prog.ml
 cat <<'OCAML'
# 42 "assertion-fixture.ml"
let original () = (fun () -> assert false)
# 100 "assertion-fixture.ml"
let require name value=if not value then failwith name
let catch thunk=try ignore(thunk());failwith "failure callback returned"with error->error
let location=function Assert_failure(file,line,column)->file,line,column|_->failwith "changed exception constructor"
let ()=
 let a=original()and b=original()and x=factory()and y=factory()in
 require "native/bytecode closure creation identity"((a==b)=(x==y));
 let old=catch a and current=catch x in
 require "exact original assertion payload"(location old=location current&&location current=("assertion-fixture.ml",42,29));
 require "new exception object at every failed call"(old!=catch a&&current!=catch x);
 let file,_,_=location old and current_file,_,_=location current in
 require "original in-unit filename pool"((file=="assertion-fixture.ml")=(current_file=="assertion-fixture.ml"));
 let check line column thunk=require "typed assertion payload"(location(catch thunk)=("assertion-fixture.ml",line,column))in
 check 43 7(boolean());check 44 11(text());check 45 3(pending());check 46 0(polymorphic());
 let allocation fn=Gc.full_major();let before=Gc.allocated_bytes()in
  for _=1 to 100000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.before in
 let before=allocation original and after=allocation factory in
 require "no extra closure factory allocation"(before=after);
 let failed_allocation fn=Gc.full_major();let before=Gc.allocated_bytes()in
  for _=1 to 100000 do ignore(Sys.opaque_identity(catch fn))done;Gc.allocated_bytes()-.before in
 let old_failure=failed_allocation a and fresh_failure=failed_allocation x in
 require "no extra failing call allocation"(old_failure=fresh_failure);
 Printf.printf "PASS: typed closed assertion factories preserve native/bytecode creation identity, original location/filename pooling, fresh synchronous failures and exact factory %.0f/%.0f and failure %.0f/%.0f B allocations.\n"before after old_failure fresh_failure
OCAML
} > check.ml
for compiler in ocamlc ocamlopt; do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml check.ml
 "./check-$compiler"
done
# The location is part of native semantics even though the logical descriptor's
# type and namespace remain unchanged. A rebuild must replace that identity.
python3 - <<'PY'
from pathlib import Path
p=Path('sites.definition');p.write_text(p.read_text().replace('word_site : unit -> unit -> PrimInt63.int := 42 29.','word_site : unit -> unit -> PrimInt63.int := 47 29.'))
PY
soma extract main.soma -no-soma-prelude -o native-changed >changed-extract.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
python3 - <<'PY'
from pathlib import Path
assert Path('hash.log').read_bytes()!=Path('changed-hash.log').read_bytes(), 'assertion coordinate change reused logical/native hash'
assert Path('native/native_abi.manifest').read_bytes()!=Path('native-changed/native_abi.manifest').read_bytes(), 'assertion coordinate change reused ABI identity'
assert '__FILE__, 47, 29' in Path('native-changed/soma_bindings.ml').read_text()
PY
printf 'PASS: assertion location changes invalidate native ABI and semantic hashes.\n'
