#!/usr/bin/env bash
# Unrelated proof relations must not change hashes of existing checked terms.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cd "$work"
export SOMA_CACHE="$work/cache"
python3 - <<'PYTEST'
from pathlib import Path
import subprocess
base = """From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String.
Inductive request := Done (value : string) | Next (rest : request).
Definition root := Done EmptyString.
Definition word := 67108864%uint63.
Theorem fixed_word : word = 67108864%uint63.
Proof. reflexivity. Qed.
Theorem fixed_root : root = root.
Proof. reflexivity. Qed.
"""
def report(source):
    implementation, proof = source.split('Theorem fixed_word', 1)
    Path('subject.soma').write_text(implementation)
    Path('subject.exp').write_text('Theorem fixed_word' + proof)
    result = subprocess.run(['soma','hash','subject.soma'], text=True, capture_output=True)
    assert result.returncode == 0, result.stderr
    return {name: (contract,witness,*assumptions) for contract,witness,name,*assumptions
            in (row.split() for row in result.stdout.splitlines())}
old = report(base)
for name in ['trace','a_trace','z_trace']:
    addition = f"""
Inductive {name} : request -> Prop :=
| Finished : forall text, {name} (Done text)
| Advanced : forall action, action = action -> {name} action -> {name} (Next action).
Theorem extra : {name} root.
Proof. constructor. Qed.
"""
    new = report(base + addition)
    for key,value in old.items():
        assert new[key] == value, (name,key,'changed after an unrelated addition',value,new[key])
    assert report(base) == old, 'removal changed the original report'
print('PASS: existing contracts, witnesses and assumptions survive added/removed recursive proof relations')
PYTEST
