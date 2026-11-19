#!/usr/bin/env bash

# An unresolvable symlink cannot safely be called an empty source tree. Fail
# with the path and operation, without leaking an uncaught Sys_error.
set -euo pipefail
export PATH="$BIN:$PATH"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
export SOMA_TEST_DIFF_UNREADABLE="$TMP"
export XDG_CACHE_HOME="$TMP/cache"

python3 - <<'PY'
import os
import pathlib
import subprocess

tmp = pathlib.Path(os.environ['SOMA_TEST_DIFF_UNREADABLE']).resolve()
for name in ('old', 'new'):
    p = tmp / name
    p.mkdir()
    (p / 'soma.toml').write_text('[project]\nname = "lib"\nversion = "1.0.0"\n')
    (p / 'main.soma').write_text('v : nat := 1.\n')

for name, target in (('self', 'self'), ('dangling', 'missing_directory')):
    link = tmp / 'old' / name
    link.symlink_to(target, target_is_directory=True)
    p = subprocess.run(['soma', 'diff', str(tmp / 'old'), str(tmp / 'new')],
                       text=True, capture_output=True, timeout=90)
    assert p.returncode != 0, (name, 'unresolved link was silently accepted', p.stdout, p.stderr)
    assert 'Cannot inspect ' in p.stderr and str(link) in p.stderr, (name, p.stderr)
    assert 'while finding files to compare' in p.stderr, (name, p.stderr)
    assert 'System error:' not in p.stderr and 'Fatal error:' not in p.stderr, (name, p.stderr)
    assert 'unchanged.' not in p.stdout, (name, p.stdout)
    link.unlink()
print('diff self-referential and dangling symlinks fail with contextual diagnostics: ok')
PY
