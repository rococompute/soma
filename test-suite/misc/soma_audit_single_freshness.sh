#!/usr/bin/env bash

# A pure single-file build has no persistent .vo output. Its trusted success
# record can still avoid rechecking unchanged source, but never changed bytes,
# expectations, configuration or a tampered record.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
export SOMA_TEST_SINGLE_FRESHNESS="$WORK"
python3 - <<'PY'
import os
import pathlib
import subprocess

work = pathlib.Path(os.environ['SOMA_TEST_SINGLE_FRESHNESS']).resolve()
root = work / 'app'
root.mkdir()
(root / 'soma.toml').write_text('[project]\nname = "single"\nversion = "0.1.0"\n')
source = root / 'main.soma'
source.write_text('value : nat := 1.\n')
env = dict(os.environ)
env.update(SOMA_CACHE=str(work / 'shared'), XDG_CACHE_HOME=str(work / 'xdg'),
           SOMA_MIRAGE_BUILD='0', SOMA_OCAML_BUILD='0')

def run(args, success=True):
    p = subprocess.run(['soma'] + args, cwd=root, env=env,
                       capture_output=True, text=True, timeout=90)
    assert (p.returncode == 0) == success, (args, p.stdout, p.stderr)
    return p

run(['build', '--check-fresh', 'main.soma'], False)
run(['build', 'main.soma'])
assert not (root / 'main.vo').exists()
assert 'unchanged' in run(['build', '--check-fresh', 'main.soma']).stdout
assert 'unchanged since its last build' in run(['build', 'main.soma']).stdout

before = source.stat()
source.write_text('value : nat := 2.\n')
os.utime(source, ns=(before.st_atime_ns, before.st_mtime_ns))
run(['build', '--check-fresh', 'main.soma'], False)
run(['build', 'main.soma'])
run(['build', '--check-fresh', 'main.soma'])
(root / 'main.exp').write_text('Theorem wrong : value = 1. Proof. reflexivity. Qed.\n')
run(['build', '--check-fresh', 'main.soma'], False)
run(['build', 'main.soma'], False)
(root / 'main.exp').unlink()
run(['build', '--check-fresh', 'main.soma'], False)
run(['build', 'main.soma'])

records = list((root / '.soma-cache' / '.freshness').iterdir())
assert len(records) == 1
records[0].write_text(records[0].read_text() + 'forged metadata\n')
run(['build', '--check-fresh', 'main.soma'], False)
run(['build', 'main.soma'])
run(['build', '--check-fresh', 'main.soma'])
print('pure single-file freshness reuses successful checks and invalidates changed inputs/records: ok')
PY
