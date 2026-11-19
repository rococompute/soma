#!/usr/bin/env bash
# The worker reports actual loaded .vo paths. Source-level Add LoadPath must
# not evade the driver's conservative fallback for external dependencies.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
export SOMA_TEST_EXTERNAL_IMPORT_FRESHNESS="$WORK"
python3 - <<'PY'
import os
import pathlib
import shutil
import subprocess

work = pathlib.Path(os.environ['SOMA_TEST_EXTERNAL_IMPORT_FRESHNESS']).resolve()
root, outside = work / 'app', work / 'outside'
root.mkdir()
outside.mkdir()
(root / 'soma.toml').write_text('[project]\nname = "external_app"\nversion = "0.1.0"\n')
(root / 'helper.soma').write_text('local : nat := 0.\n')
(root / 'main.soma').write_text(
    'Import helper.\nAdd LoadPath "%s" as External.\n'
    'From External Require Import Dep.\nmain := value.\n' % str(outside).replace('"', '""'))
env = dict(os.environ)
env.update(SOMA_CACHE=str(work / 'shared'), XDG_CACHE_HOME=str(work / 'xdg'),
           SOMA_OCAML_BUILD='0', SOMA_MIRAGE_BUILD='0')
rocq = shutil.which('rocq')
assert rocq, 'the test needs rocq from the same installation as soma'
for value in (1, 2):
    (outside / 'Dep.v').write_text('Definition value : nat := %d.\n' % value)
    p = subprocess.run([rocq, 'c', '-Q', str(outside), 'External', 'Dep.v'], cwd=outside,
                       env=env, text=True, capture_output=True, timeout=90)
    assert p.returncode == 0, (p.stdout, p.stderr)
    p = subprocess.run(['soma', 'build', 'main.soma'], cwd=root, env=env,
                       text=True, capture_output=True, timeout=90)
    assert p.returncode == 0, (p.stdout, p.stderr)
    p = subprocess.run(['soma', 'build', '--check-fresh', 'main.soma'], cwd=root, env=env,
                       text=True, capture_output=True, timeout=90)
    assert p.returncode != 0, ('external loaded objects were incorrectly certified', p.stdout, p.stderr)
print('actual external Require paths remain uncertified for whole-build skipping: ok')
PY
