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
parts=[{extract="source",kind="source-types",namespace="exports",expect=[{names=["flag"],target=""}]}]
[build.unit.public]
output="public.ml"
parts=[{whitespace="\n"},{unit="prefix"},{extract="source",kind="aliases",namespace="exports",expect=[{names=["L"],target="Stdlib.List"}]},{extract="source",kind="bindings",namespace="exports",expect=[{names=["id"],target="exports.identity"}]},{whitespace=" \t\n"}]
[build.source-map.spans]
output="public.ml.soma-parts.toml"
unit="public"
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
[build.module-list.closed]
output="closed.sexp"
units=["public"]
[build.dune.native]
directory="."
targets=["check.exe","check.bc"]
needs=["closed","signature","certificate","forward","spans"]
TOML
cat >dune-project <<'DUNE'
(lang dune 3.13)
DUNE
cat >dune <<'DUNE'
(rule (target public.ml) (deps products/public.ml) (action (copy %{deps} %{target})))
(executable (name check) (modules check (:include products/closed.sexp)) (modes exe byte))
DUNE
printf 'this is deliberately invalid unowned OCaml\n' >rogue.ml
cat >check.ml <<'ML'
let () =
  let flag : Public.flag = true in assert flag;
  assert (Public.L.length [1;2] = 2);
  let bytes=Bytes.of_string "same object" in assert (Public.id bytes == bytes);
  assert (Public.id 7 = 7 && Public.id "generic" = "generic");
  print_endline "PASS: native project graph preserves types, aliases, generic values and identity"
ML
soma project plan >plan.log
printf 'source: \ncertificate: source\nprefix: source\npublic: prefix source\nclosed: public\nwhole: source\nforward: whole\nsignature: source\nspans: public\nnative: certificate closed forward signature spans\n' >expected-plan
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
verification=tomllib.loads(Path('products/checked.verification.toml').read_text())
imports=verification['project-imports']
assert any(row['file']=='exports.definition' for row in imports)
assert all(len(row['inputs-sha256'])==64 for row in imports)
for name in ['public','whole','signature','certificate','forward']:
 receipt=tomllib.loads(Path('products/.receipts/'+name+'.toml').read_text())
 assert receipt['verification']==[{'extract':'source','sha256':proof}]
assert Path('products/closed.sexp').read_text()=='("Public")\n'
closed=tomllib.loads(Path('products/.receipts/closed.toml').read_text())
assert closed['units']==[{'unit':'public','receipt-sha256':hashlib.sha256(Path('products/.receipts/public.toml').read_bytes()).hexdigest()}]
spans=tomllib.loads(Path('products/public.ml.soma-parts.toml').read_text())
data=Path('products/public.ml').read_bytes()
assert spans['output']=='public.ml' and spans['sha256']==hashlib.sha256(data).hexdigest()
assert spans['unit-receipt-sha256']==hashlib.sha256(Path('products/.receipts/public.toml').read_bytes()).hexdigest()
cursor=0
for part in spans['parts']:
 if 'whitespace' in part:
  value=part['whitespace'].encode(); assert not value.strip(b' \t\r\n')
 else:
  extract,file=part['artifact'].split('/',1)
  value=Path('products/.extract',extract,file).read_bytes()
  assert part['size']==len(value) and part['sha256']==hashlib.sha256(value).hexdigest()
 assert data[cursor:cursor+len(value)]==value
 cursor+=len(value)
assert cursor==len(data)
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
# Audit recomputes evidence and whole outputs instead of trusting old receipts.
soma project audit >audit.log 2>&1
cmp products/public.ml previous.ml
cmp products/.receipts/public.toml previous-receipt.toml
test ! products/.extract/source/prog.ml -nt previous-prog.ml
printf '\n(* tampered publication *)\n' >>products/public.ml
cp products/public.ml tampered.ml
if soma project audit >audit-product.log 2>&1; then exit 1; fi
grep -q 'published product differs from fresh checking' audit-product.log
cmp products/public.ml tampered.ml
cp previous.ml products/public.ml
printf '\n' >>products/.receipts/public.toml
cp products/.receipts/public.toml tampered-receipt.toml
if soma project audit >audit-receipt.log 2>&1; then exit 1; fi
grep -q 'published receipt differs from fresh checking' audit-receipt.log
cmp products/.receipts/public.toml tampered-receipt.toml
cp previous-receipt.toml products/.receipts/public.toml
cp products/public.ml.soma-parts.toml previous-map.toml
printf '\n' >>products/public.ml.soma-parts.toml
cp products/public.ml.soma-parts.toml tampered-map.toml
if soma project audit --target spans >audit-map.log 2>&1; then exit 1; fi
grep -q 'published source map differs from fresh checking' audit-map.log
cmp products/public.ml.soma-parts.toml tampered-map.toml
cp previous-map.toml products/public.ml.soma-parts.toml
cp main.exp previous-exp
printf '\n(* changed proof input *)\n' >>main.exp
if soma project audit --target public >audit-source.log 2>&1; then exit 1; fi
grep -q 'published receipt differs from fresh checking' audit-source.log
cmp products/public.ml previous.ml
cp previous-exp main.exp
cp exports.definition previous-definition
printf '\n(* changed imported declaration input *)\n' >>exports.definition
if soma project audit --target public >audit-declaration.log 2>&1; then exit 1; fi
grep -q 'published receipt differs from fresh checking' audit-declaration.log
cmp products/public.ml previous.ml
cmp products/.receipts/public.toml previous-receipt.toml
cp previous-definition exports.definition
# A valid source edit can still break a consumer's declared publication API.
for change in type-name alias-target value-name; do
 cp exports.definition export-before
 cp main.soma source-before
 cp main.exp proof-before
 case "$change" in
  type-name) sed 's/As "flag"/As "different"/' export-before >exports.definition ;;
  alias-target) sed 's/Stdlib.List/Stdlib.Array/' export-before >exports.definition ;;
  value-name)
   sed 's/Reexport Value id :=/Reexport Value renamed :=/' export-before >exports.definition
   sed 's/,id)/,renamed)/' source-before >main.soma
   sed 's/: id=tt/: renamed=tt/' proof-before >main.exp ;;
 esac
 if soma project build --target public >"contract-$change.log" 2>&1; then exit 1; fi
 grep -q 'export contract differs' "contract-$change.log"
 cmp products/public.ml previous.ml
 cmp products/.receipts/public.toml previous-receipt.toml
 cp export-before exports.definition
 cp source-before main.soma
 cp proof-before main.exp
done
test -z "$(find products/.extract -name '*.stage*' -print)"
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
[build.module-list.pair]
output="pair.sexp"
units=["whole","signature"]
TOML
soma project build --target padded --target pair >padded.log 2>&1
python3 - <<'PY'
from pathlib import Path
import tomllib
assert Path('products/padded.ml').read_bytes()==b'\n'+Path('products/complete.ml').read_bytes()+b'\n'
r=tomllib.loads(Path('products/.receipts/padded.toml').read_text())
assert r['parts'][0]==r['parts'][-1]=={'whitespace':'\n'}
assert Path('products/pair.sexp').read_text()=='("Complete")\n'
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
