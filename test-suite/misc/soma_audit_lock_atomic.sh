#!/usr/bin/env bash

# An already-open reader of soma.lock must keep its complete snapshot when
# another build updates a checkout dependency's version. This deterministically
# distinguishes atomic publication from truncating and rewriting the same inode.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
export SOMA_TEST_LOCK_ATOMIC="$TMP"
export SOMA_CACHE="$TMP/cache"

python3 - <<'PY'
import os
import pathlib
import stat
import subprocess
import tomllib

tmp = pathlib.Path(os.environ['SOMA_TEST_LOCK_ATOMIC']).resolve()
project = tmp / 'project'
dep = tmp / 'dep'
project.mkdir()
dep.mkdir()
(project / 'soma.toml').write_text(
    '[project]\nname = "app"\nversion = "0.1.0"\n'
    '[dependencies]\n"owner/dep" = { path = "../dep" }\n')
(project / 'main.soma').write_text('Import dep.a.\nv.\n')
(dep / 'a.soma').write_text('v : nat := 1.\n')

def version(v):
    (dep / 'soma.toml').write_text(
        '[project]\nname = "dep"\nversion = "%s"\n' % v)

def build():
    p = subprocess.run(['soma', 'build', 'main.soma'], cwd=project,
                       text=True, capture_output=True, timeout=90)
    assert p.returncode == 0, (p.stdout, p.stderr)

version('1.0.0')
build()
lock = project / 'soma.lock'
old = lock.read_bytes()
assert tomllib.loads(old.decode())['resolved'][0]['version'] == '1.0.0'
lock.chmod(0o640)
before = lock.stat()
with lock.open('rb') as reader:
    version('1.1.0')
    build()
    assert reader.read() == old, 'an open reader saw its lock snapshot overwritten'
new = lock.read_bytes()
assert tomllib.loads(new.decode())['resolved'][0]['version'] == '1.1.0'
assert lock.stat().st_ino != before.st_ino, 'publication reused the old inode'
assert stat.S_IMODE(lock.stat().st_mode) == 0o640, 'lock permissions changed'
assert not list(project.glob('.soma-lock-*.tmp')), 'publication left temporary files'

# A matching lock is not rewritten: builds should not churn its identity/mtime.
unchanged = lock.stat()
build()
after = lock.stat()
assert (after.st_ino, after.st_mtime_ns) == (unchanged.st_ino, unchanged.st_mtime_ns)
assert lock.read_bytes() == new

# A preexisting symlink is replaced, not followed while publishing. Its target
# remains an old complete snapshot rather than being overwritten outside root.
outside = tmp / 'outside.lock'
outside.write_bytes(new)
lock.unlink()
lock.symlink_to(outside)
version('1.2.0')
build()
assert not lock.is_symlink(), 'lock publication retained a symlink'
assert outside.read_bytes() == new, 'publication overwrote a symlink target'
assert tomllib.loads(lock.read_text())['resolved'][0]['version'] == '1.2.0'
assert not list(project.glob('.soma-lock-*.tmp'))
print('atomic lock publication: open-reader snapshot, mode, unchanged lock and symlink target: ok')
PY
