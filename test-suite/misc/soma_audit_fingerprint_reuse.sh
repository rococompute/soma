#!/usr/bin/env bash
# Reuse only the immutable initial installation snapshot. Sources at the
# pre-build boundary must still be read, and final validation must rescan.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
export SOMA_TEST_FINGERPRINT_REUSE="$WORK"
python3 - <<'PY'
import hashlib
import os
import pathlib
import subprocess
import threading
import time

work = pathlib.Path(os.environ['SOMA_TEST_FINGERPRINT_REUSE']).resolve()
root = work / 'app'
root.mkdir()
(root / 'soma.toml').write_text('[project]\nname="reuse"\nversion="0.1.0"\n')
# Leave enough time after receipt removal for the writer to replace source
# before the snapshot reaches it. This is data, not compiler source/work.
(root / '000_padding.bin').write_bytes(b'\0' * (32 * 1024 * 1024))
trace = work / 'fingerprints.tsv'
env = dict(os.environ, SOMA_OCAML_BUILD='0', SOMA_MIRAGE_BUILD='0', SOMA_PROOF_JOBS='0',
           SOMA_CACHE=str(work / 'shared'), XDG_CACHE_HOME=str(work / 'xdg'),
           SOMA_TEST_FINGERPRINT_LOG=str(trace))

def source(value):
    for name, contents in (
        ('main.soma', 'value : nat := %d.\n' % value),
        ('main.exp', 'Theorem value_is : value = %d. Proof. reflexivity. Qed.\n' % value)):
        temporary = work / (name + '.next')
        temporary.write_text(contents)
        os.replace(temporary, root / name)

def build():
    p = subprocess.run(['soma', 'build', 'main.soma'], cwd=root, env=env,
                       capture_output=True, text=True, timeout=120)
    assert p.returncode == 0, (p.stdout, p.stderr)

source(1)
build()
receipts = list((root / '.soma-cache' / '.freshness').glob('*'))
assert len(receipts) == 1
receipt = receipts[0]
source(2)
trace.write_text('')
changed, stop = threading.Event(), threading.Event()

def edit_at_snapshot_boundary():
    while receipt.exists():
        if stop.wait(0.0005):
            return
    source(3)
    changed.set()

writer = threading.Thread(target=edit_at_snapshot_boundary)
writer.start()
try:
    start = time.monotonic()
    build()
    elapsed = time.monotonic() - start
finally:
    stop.set()
    writer.join(timeout=5)
assert changed.is_set(), 'source replacement did not reach the pre-build boundary'
rows = [line.split('\t') for line in trace.read_text().splitlines()]
assert len(rows) == 4, ('expected one initial and one final scan of both trees', rows)
assert sorted(row[0] for row in rows) == ['coqlib', 'coqlib', 'runtimelib', 'runtimelib']
p = subprocess.run(['soma', 'build', '--check-fresh', 'main.soma'], cwd=root, env=env,
                   capture_output=True, text=True, timeout=120)
assert p.returncode == 0, (p.stdout, p.stderr)
contents = receipt.read_text()
for name in ('main.soma', 'main.exp'):
    digest = hashlib.sha256((root / name).read_bytes()).hexdigest()
    assert 'source "./%s" %s' % (name, digest) in contents, contents
print('installation snapshot reused; changed source/proofs captured; independent final scan retained: ok')
print('build %.3fs; two tree snapshots %.3fs' % (elapsed, sum(float(row[1]) for row in rows)))
PY
