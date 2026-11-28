#!/usr/bin/env bash
# Real checker -> declarative graph -> native/bytecode compilation, without Python.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >exports.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native Reexport Type public_flag As "flag" := bool.
OCaml Native Module Alias L := "Stdlib.List".
OCaml Native External Value identity : forall A:Type,A -> A := "Stdlib.Fun.id".
OCaml Native Reexport Value id := identity.
SOMA
cat >main.soma <<'SOMA'
Import exports.
Definition main := (public_flag,L,id).
Verification Properties "public_identity_checked" Invariants "" Trust "".
SOMA
cat >main.exp <<'SOMA'
Theorem public_identity_checked : id=tt.
Proof. reflexivity. Qed.
SOMA
cat >soma.toml <<'TOML'
[project]
name="graph_test"
version="0.1.0"
[build]
directory="products"
targets=["native"]
[build.extract.source]
file="main.soma"
verify=true
options=["-no-soma-prelude"]
[build.unit.prefix]
output="prefix.ml"
parts=[{extract="source",kind="source-types",namespace="exports"}]
[build.unit.public]
output="public.ml"
parts=[{unit="prefix"},{extract="source",kind="aliases",namespace="exports"},{extract="source",kind="values",namespace="exports"}]
[build.publish.whole]
extract="source"
file="prog.ml"
output="complete.ml"
[build.publish.signature]
extract="source"
file="prog.mli"
output="complete.mli"
[build.publish.certificate]
extract="source"
file="verification.toml"
output="checked.verification.toml"
[build.unit.forward]
output="forward.ml"
parts=[{unit="whole"}]
[build.dune.native]
directory="."
targets=["check.exe","check.bc"]
needs=["public","signature","certificate","forward"]
TOML
cat >dune-project <<'DUNE'
(lang dune 3.13)
DUNE
cat >dune <<'DUNE'
(rule (target public.ml) (deps products/public.ml) (action (copy %{deps} %{target})))
(executable (name check) (modules check public) (modes exe byte))
DUNE
cat >check.ml <<'ML'
let () =
  let flag : Public.flag = true in assert flag;
  assert (Public.L.length [1;2] = 2);
  let bytes=Bytes.of_string "same object" in assert (Public.id bytes == bytes);
  assert (Public.id 7 = 7 && Public.id "generic" = "generic");
  print_endline "PASS: native project graph preserves types, aliases, generic values and identity"
ML
soma project plan >plan.log
printf 'source: \ncertificate: source\nwhole: source\nforward: whole\nprefix: source\npublic: prefix source\nsignature: source\nnative: certificate forward public signature\n' >expected-plan
cmp plan.log expected-plan
soma project build >build.log 2>&1
cmp products/.extract/source/prog.ml products/complete.ml
cmp products/.extract/source/prog.mli products/complete.mli
cmp products/complete.ml products/forward.ml
cmp products/.extract/source/verification.toml products/checked.verification.toml
python3 - <<'PY'
from pathlib import Path
import hashlib,tomllib
proof=hashlib.sha256(Path('products/checked.verification.toml').read_bytes()).hexdigest()
for name in ['public','whole','signature','certificate','forward']:
 receipt=tomllib.loads(Path('products/.receipts/'+name+'.toml').read_text())
 assert receipt['verification']==[{'extract':'source','sha256':proof}]
PY
_build/default/check.exe
_build/default/check.bc
cp products/public.ml previous.ml
cp products/.receipts/public.toml previous-receipt.toml
cp -p products/.extract/source/prog.ml previous-prog.ml
soma project build >repeat.log 2>&1
grep -q 'unchanged .*public.ml' repeat.log
cmp products/public.ml previous.ml
cmp products/.receipts/public.toml previous-receipt.toml
test ! products/.extract/source/prog.ml -nt previous-prog.ml
# Same unit through two graph edges must not duplicate runtime initialization.
cp soma.toml previous-config
cat >>soma.toml <<'TOML'
[build.unit.duplicate]
output="public-again.ml"
parts=[{unit="public"},{unit="prefix"}]
TOML
if soma project build --target duplicate >duplicate.log 2>&1; then exit 1; fi
grep -q 'duplicate whole artifact' duplicate.log
test ! -e products/public-again.ml
cmp products/public.ml previous.ml
mv previous-config soma.toml
# Preserve only ASCII spacing between complete compiler products.
cp soma.toml previous-config
cat >>soma.toml <<'TOML'
[build.unit.padded]
output="padded.ml"
parts=[{whitespace="\n"},{unit="whole"},{whitespace="\n"}]
TOML
soma project build --target padded >padded.log 2>&1
python3 - <<'PY'
from pathlib import Path
import tomllib
assert Path('products/padded.ml').read_bytes()==b'\n'+Path('products/complete.ml').read_bytes()+b'\n'
r=tomllib.loads(Path('products/.receipts/padded.toml').read_text())
assert r['parts'][0]==r['parts'][-1]=={'whitespace':'\n'}
PY
mv previous-config soma.toml
# A named input must exist as a complete file in the fresh checked extraction.
cp soma.toml previous-config
cat >>soma.toml <<'TOML'
[build.publish.absent]
extract="source"
file="does-not-exist.ml"
output="absent.ml"
TOML
if soma project build --target absent >absent.log 2>&1; then exit 1; fi
test ! -e products/absent.ml
cmp products/public.ml previous.ml
mv previous-config soma.toml
# Removing the complete declaration cannot turn a verified graph into a
# successful unverified extraction, or replace its previous checked products.
cp main.soma previous-source
sed '/^Verification /d' previous-source >main.soma
if soma project build >missing-policy.log 2>&1; then exit 1; fi
grep -q 'no source-owned Verification policy' missing-policy.log
cmp products/public.ml previous.ml
cmp products/.extract/source/prog.ml previous-prog.ml
mv previous-source main.soma
# A failed proof recheck cannot publish a changed unit or extraction.
cp products/.extract/source/prog.ml previous-prog.ml
printf '\nTheorem impossible : False. Proof. exact I. Qed.\n' >>main.exp
if soma project build >failed.log 2>&1; then exit 1; fi
cmp products/public.ml previous.ml
cmp products/.extract/source/prog.ml previous-prog.ml
test -z "$(find products/.extract -name '*.stage*' -print)"
echo 'PASS: unchanged publication, duplicate initialization rejection, failed proof rollback/cleanup'
