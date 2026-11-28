#!/usr/bin/env bash
# Real publication ABI contracts survive implementation edits and reject API drift.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 25 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
Definition fields := Native.Export (Native.Return (true, false)).
Definition main := fields.
OCaml Native Public Projection main From fields As "(left, right)".
Verification Properties "main_is_fields" Invariants "" Trust "Corelib.Numbers.Cyclic.Int63.PrimInt63.int".
SOMA
cat >main.exp <<'SOMA'
Theorem main_is_fields : main = fields.
Proof. reflexivity. Qed.
SOMA
cat >soma.toml <<'TOML'
[project]
name="native_abi_contract_test"
version="0.1.0"
[build]
directory="products"
targets=["implementation","signature"]
source-only=true
[build.extract.source]
file="main.soma"
verify=true
options=["-no-soma-prelude"]
[build.publish.implementation]
extract="source"
file="main.assembly"
output="public.ml"
[build.publish.signature]
extract="source"
file="main.assembly-interface"
output="public.mli"
TOML
soma project build >baseline.log 2>&1
soma project abi --directory products/.extract/source >abi.toml
python3 - <<'PY'
from pathlib import Path
import tomllib
rows=tomllib.loads(Path('abi.toml').read_text())['abi']
selected=[r for r in rows if r['symbol']=='main.main'];assert len(selected)==1
text=Path('soma.toml').read_text();row=selected[0]
text=text.replace('file="main.soma"', 'file="main.soma"\nabi=[{symbol="main.main",sha256="'+row['sha256']+'"}]')
Path('soma.toml').write_text(text)
PY
soma project build >contract.log 2>&1
soma project audit >audit.log 2>&1
# Source freshness remains enforced, while the API contract permits benign edits.
printf '\n(* source comment changes no ABI *)\n' >>main.soma
soma project build >comment.log 2>&1
soma project abi --directory products/.extract/source >comment-abi.toml
cmp abi.toml comment-abi.toml
cp main.soma original-source
sed 's/(true, false)/(false, true)/' original-source >main.soma
soma project build >implementation.log 2>&1
soma project abi --directory products/.extract/source >implementation-abi.toml
cmp abi.toml implementation-abi.toml
cp main.soma original-source
cp products/public.ml previous.ml
cp products/public.mli previous.mli
cp products/.receipts/implementation.toml previous-receipt
cp products/.extract/source/prog.ml previous-prog
for change in missing rename member; do
 case "$change" in
  missing) sed '/^OCaml Native Public Projection/d' original-source >main.soma ;;
  rename) sed 's/(left, right)/(first, right)/' original-source >main.soma ;;
  member) sed 's/(left, right)/(left, _)/' original-source >main.soma ;;
 esac
 if soma project build >"$change.log" 2>&1; then exit 1; fi
 grep -Eq 'missing native ABI contract symbol|native ABI contract differs' "$change.log"
 grep -q 'OCaml: extracted main.soma' "$change.log"
 cmp products/public.ml previous.ml
 cmp products/public.mli previous.mli
 cmp products/.receipts/implementation.toml previous-receipt
 cmp products/.extract/source/prog.ml previous-prog
 if soma project audit >"audit-$change.log" 2>&1; then exit 1; fi
 grep -Eq 'missing native ABI contract symbol|native ABI contract differs' "audit-$change.log"
 cmp products/public.ml previous.ml
 cp original-source main.soma
done
test -z "$(find products/.extract -name '*.stage*' -print)"
# Inspection also refuses an altered or unindexed manifest; it cannot bless it.
cp products/.extract/source/native_abi.manifest original-abi
printf '\n' >>products/.extract/source/native_abi.manifest
if soma project abi --directory products/.extract/source >tamper.log 2>&1; then exit 1; fi
grep -q 'content hash differs' tamper.log
cp original-abi products/.extract/source/native_abi.manifest
echo 'PASS: real native ABI contracts, source/implementation flexibility, missing/changed APIs, atomic rejection and authenticated inspection'
