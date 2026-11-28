#!/usr/bin/env bash
# Compiler-owned obligations, independent of a Python policy dictionary.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >main.soma <<'SOMA'
From Stdlib Require Import Arith.
Inductive tree := Node (children : forest) with forest := Nil | Cons (t : tree) (children : forest).
Definition main (n:nat) := n+0.
Definition policy_anchor := tt.
SOMA
cat >main.exp <<'SOMA'
Theorem trace : forall n, main n=n+0.
Proof. intros; reflexivity. Qed.
Theorem preserves_input : forall n, main n=n.
Proof. intro n; unfold main; apply Nat.add_0_r. Qed.
SOMA
cp main.soma plain.soma.txt
cp main.exp good.exp.txt
soma extract main.soma -no-soma-prelude -o baseline >baseline.log 2>&1
cat >>main.soma <<'SOMA'
Verification Properties "trace" Invariants "preserves_input" Trust "".
SOMA
cp main.soma good.soma.txt
soma verify "$work/main.soma" -no-soma-prelude >verify.log 2>&1
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >definitions.hash 2>hash.log
cmp baseline/prog.ml native/prog.ml
cmp baseline/prog.mli native/prog.mli
python3 - <<'PY'
from pathlib import Path
import hashlib,tomllib
r=tomllib.loads(Path('native/verification.toml').read_text())
assert r['module']=='main' and r['property-count']==1 and r['invariant-count']==1
assert r['trusted']==[] and r['used-assumptions']==[]
assert r['properties'][0]['name']=='trace' and r['invariants'][0]['name']=='preserves_input'
reported={fields[2]:fields[:2] for line in Path('definitions.hash').read_text().splitlines() if (fields:=line.split())}
for row in r['definitions']:
 assert reported[row['name']]==[row['contract'],row['witness']],row['name']
assert {'main.tree','main.forest'} <= reported.keys()
for row in r['properties']+r['invariants']:
 assert len(row['contract'])==len(row['witness'])==64 and row['assumptions']==[]
for row in r['inputs']:
 p=Path(row['file'])
 assert row['sha256']==(hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else 'absent')
Path('before.sha').write_text(hashlib.sha256(Path('native/prog.ml').read_bytes()).hexdigest())
PY
reject() {
  local expected=$1
  if soma extract main.soma -no-soma-prelude -o native >failure.log 2>&1; then
    echo 'accepted invalid source verification policy' >&2; exit 1
  fi
  grep -q "$expected" failure.log
  cmp baseline/prog.ml native/prog.ml
  cmp baseline/prog.mli native/prog.mli
}
sed 's/Theorem trace /Theorem renamed_trace /' good.exp.txt >main.exp
reject 'required property main.trace is missing'
sed 's/Theorem preserves_input /Theorem renamed_invariant /' good.exp.txt >main.exp
reject 'required invariant main.preserves_input is missing'
cp good.exp.txt main.exp
printf 'Reset policy_anchor.\n' >main.exp
cat good.exp.txt >>main.exp
reject 'source Verification policy changed while checking expectations'
cp good.exp.txt main.exp
printf '\nTheorem unchecked : False. Admitted.\n' >>main.exp
reject 'untrusted assumptions'
cp good.exp.txt main.exp
printf '\nAxiom unmentioned : False.\n' >>main.exp
reject 'untrusted assumptions'
cp good.exp.txt main.exp
printf '\nFrom Corelib.Gradual Require Import Gradual.\nDefinition gradual : nat := unk.\n' >>main.exp
reject 'gradual evidence is not permitted'
sed 's/Trust ""/Trust "Corelib.Gradual.Gradual.unknown"/' good.soma.txt >main.soma
reject 'gradual evidence is not permitted'
cp good.soma.txt main.soma
cp good.exp.txt main.exp
printf '\nUnset Guard Checking.\nDefinition unchecked_flags : nat := 0.\n' >>main.exp
reject 'untrusted assumptions: main.unchecked_flags (no guard check)'
cp good.exp.txt main.exp
sed 's/Properties "trace"/Properties "main"/' good.soma.txt >main.soma
reject 'not a proposition'
cp good.soma.txt main.soma
printf '\nTheorem concrete : True. Proof. exact I. Qed.\n' >>main.exp
sed 's/Invariants "preserves_input"/Invariants "concrete"/' good.soma.txt >main.soma
reject 'must quantify over inputs'
cp good.exp.txt main.exp
cp plain.soma.txt main.soma
if soma verify main.soma -no-soma-prelude >missing.log 2>&1; then exit 1; fi
grep -q 'no source-owned Verification policy' missing.log
cat >>main.exp <<'SOMA'
Verification Properties "trace" Invariants "preserves_input" Trust "".
SOMA
reject 'declare the policy in the source program'
# Quantification may be hidden behind a transparent proposition alias.
cp good.soma.txt main.soma
cat >main.exp <<'SOMA'
Theorem trace : forall n, main n=n+0.
Proof. intros; reflexivity. Qed.
Definition identity_spec := forall n, main n=n.
Theorem preserves_input : identity_spec.
Proof. intro n; unfold main; apply Nat.add_0_r. Qed.
SOMA
soma verify main.soma -no-soma-prelude >alias.log 2>&1
# The complete root must audit even unused definitions from cached imports.
cat >dependency.soma <<'SOMA'
Definition unused := 0.
SOMA
cat >dependency.exp <<'SOMA'
Axiom untrusted : False.
SOMA
soma check dependency.soma -no-soma-prelude >dependency.log 2>&1
printf 'Import dependency.\n' >main.soma
cat good.soma.txt >>main.soma
reject 'untrusted assumptions: dependency.untrusted'
printf 'Theorem valid : True. Proof. exact I. Qed.\n' >dependency.exp
soma check dependency.soma -no-soma-prelude >dependency-valid.log 2>&1
soma extract main.soma -no-soma-prelude -o cached-unverified >cached-unverified.log 2>&1
if SOMA_REQUIRE_VERIFICATION=1 soma extract main.soma -no-soma-prelude -o native >all-policies.log 2>&1; then exit 1; fi
grep -q 'dependency has no source-owned Verification policy' all-policies.log
cmp baseline/prog.ml native/prog.ml
cat >>dependency.soma <<'SOMA'
Verification Properties "valid" Invariants "" Trust "".
SOMA
SOMA_REQUIRE_VERIFICATION=1 soma extract main.soma -no-soma-prelude -o native >all-checked.log 2>&1
cp native/prog.ml baseline/prog.ml
cp native/prog.mli baseline/prog.mli
# A dependency's source-owned policy is enforced by its complete proof worker.
sed 's/Properties "valid"/Properties "missing"/' dependency.soma >dependency-next
mv dependency-next dependency.soma
reject 'required property dependency.missing is missing'
# A transitive proof loaded from a statements-only Rocq library cannot be
# treated as assumption-free merely because its body cannot be inspected.
cat >External.v <<'SOMA'
Theorem hidden : False. Proof. exact I. Qed.
SOMA
rocq c -q -vos External.v >opaque-library.log 2>&1
cp External.vos External.vo
printf 'Require Import External.\n' >main.soma
cat good.soma.txt >>main.soma
cp good.exp.txt main.exp
printf '\nDefinition escaped : False := External.hidden.\n' >>main.exp
reject 'opaque proof body is unavailable'
# Successful extraction without a policy must not retain a stale certificate.
cp plain.soma.txt main.soma
cp good.exp.txt main.exp
soma extract main.soma -no-soma-prelude -o native >plain.log 2>&1
test ! -e native/verification.toml
echo 'PASS: native obligations, static evidence, cached imports, mandatory policy, companion sealing, receipts and unchanged product bytes'
# Imported project identities must survive crossing a dependency's cache/root.
mkdir provider consumer
cat >provider/soma.toml <<'TOML'
[project]
name="provider"
version="0.1.0"
TOML
cat >provider/policy.soma <<'SOMA'
Definition value : nat := 1.
Verification Properties "valid" Invariants "" Trust "".
SOMA
printf 'Theorem valid : value=1. Proof. reflexivity. Qed.\n' >provider/policy.exp
cat >consumer/soma.toml <<'TOML'
[project]
name="consumer"
version="0.1.0"
[dependencies]
"fixture/provider"={path="../provider"}
TOML
cat >consumer/main.soma <<'SOMA'
Import provider.policy.
Definition main := value.
Verification Properties "valid" Invariants "" Trust "".
SOMA
printf 'Theorem valid : main=value. Proof. reflexivity. Qed.\n' >consumer/main.exp
(
 cd consumer
 SOMA_REQUIRE_VERIFICATION=1 soma extract main.soma -no-soma-prelude -o first >../dependency-first.log 2>&1
 printf '\n(* changed dependency source *)\n' >>../provider/policy.soma
 SOMA_REQUIRE_VERIFICATION=1 soma extract main.soma -no-soma-prelude -o second >../dependency-second.log 2>&1
 cmp first/prog.ml second/prog.ml
 python3 - <<'PY'
from pathlib import Path
import tomllib
before=tomllib.loads(Path('first/verification.toml').read_text())['project-imports']
after=tomllib.loads(Path('second/verification.toml').read_text())['project-imports']
assert any(row['file'].endswith('/provider/policy.soma') for row in before)
assert before!=after, 'dependency source change disappeared from native verification receipt'
PY
)
echo 'PASS: native receipts bind external project source identities independently of runtime bytes'
