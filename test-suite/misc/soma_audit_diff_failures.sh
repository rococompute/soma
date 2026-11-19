#!/usr/bin/env bash

# An incomplete comparison retains its useful partial report, but must not
# return the success status of a complete, possibly empty, comparison.
set -euo pipefail
export PATH="$BIN:$PATH"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
export SOMA_TEST_DIFF_FAILURES="$TMP"
export XDG_CACHE_HOME="$TMP/cache"

python3 - <<'PY'
import os
import pathlib
import subprocess

tmp = pathlib.Path(os.environ['SOMA_TEST_DIFF_FAILURES']).resolve()
for name in ('old', 'new'):
    p = tmp / name
    p.mkdir()
    (p / 'soma.toml').write_text('[project]\nname = "lib"\nversion = "1.0.0"\n')
    (p / 'fine.soma').write_text('same : nat := 1.\n')
    (p / 'edit.soma').write_text('value : nat := %d.\n' % (1 if name == 'old' else 2))
    (p / 'broken.soma').write_text('value : nat := 1.\n')

def compare(old, new):
    return subprocess.run(['soma', 'diff', str(old), str(new)],
                          text=True, capture_output=True, timeout=90)

old, new = tmp / 'old', tmp / 'new'
p = compare(old, new)
assert p.returncode == 0, (p.stdout, p.stderr)
assert '2 unchanged.' in p.stdout
(new / 'broken.soma').write_text('value : nat := true.\n')
for left, right in ((old, new), (new, old)):
    p = compare(left, right)
    assert p.returncode != 0, ('incomplete comparison succeeded', p.stdout, p.stderr)
    assert 'Not compared, as it does not compile in new:' in p.stdout, p.stdout
    assert 'broken' in p.stdout, p.stdout
    assert 'Edited:' in p.stdout and 'edit.value' in p.stdout, p.stdout
    assert '1 unchanged.' in p.stdout, p.stdout
    assert 'The comparison is incomplete' in p.stderr, p.stderr
    assert 'Removed:' not in p.stdout and 'Added:' not in p.stdout, p.stdout
print('incomplete diffs fail in either direction while retaining partial reports: ok')
PY
