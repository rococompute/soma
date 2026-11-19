#!/usr/bin/env bash

# soma diff walks source names, including acyclic aliases, without following
# a directory symlink back into an ancestor indefinitely.
set -euo pipefail
export PATH="$BIN:$PATH"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
export SOMA_TEST_DIFF_CYCLES="$TMP"
export XDG_CACHE_HOME="$TMP/cache"

python3 - <<'PY'
import os
import pathlib
import subprocess

tmp = pathlib.Path(os.environ['SOMA_TEST_DIFF_CYCLES']).resolve()
for name in ('old', 'new'):
    p = tmp / name
    (p / 'nested').mkdir(parents=True)
    (p / 'soma.toml').write_text('[project]\nname = "lib"\nversion = "1.0.0"\n')
    (p / 'nested' / 'a.soma').write_text('v : nat := 1.\n')
    (p / 'alias').symlink_to('nested', target_is_directory=True)

def compare(label):
    p = subprocess.run(['soma', 'diff', str(tmp / 'old'), str(tmp / 'new')],
                       text=True, capture_output=True, timeout=90)
    assert p.returncode == 0, (label, p.stdout, p.stderr)
    assert '2 unchanged.' in p.stdout, (label, p.stdout, p.stderr)
    assert 'Not compared' not in p.stdout, (label, p.stdout, p.stderr)

compare('both acyclic aliases are compared')
for name in ('old', 'new'):
    p = tmp / name
    (p / 'nested' / 'again').symlink_to('.', target_is_directory=True)
compare('cycles beneath both directory aliases terminate')
compare('repeated comparison remains stable')
print('diff directory cycles terminate and acyclic aliases remain compared: ok')
PY
