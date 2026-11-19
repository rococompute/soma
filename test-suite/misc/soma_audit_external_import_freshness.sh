#!/usr/bin/env bash
# Loading external source must not evade the driver's conservative fallback
# for dependencies outside its source snapshot and fingerprinted installation.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
export SOMA_TEST_EXTERNAL_IMPORT_FRESHNESS="$WORK"
python3 - <<'PY'
import os
import pathlib
import subprocess

work = pathlib.Path(os.environ['SOMA_TEST_EXTERNAL_IMPORT_FRESHNESS']).resolve()
root, outside = work / 'app', work / 'outside'
root.mkdir()
outside.mkdir()
(root / 'soma.toml').write_text('[project]\nname = "external_app"\nversion = "0.1.0"\n')
(root / 'helper.soma').write_text('local_value : nat := 0.\n')
(root / 'main.soma').write_text(
    'Import helper.\nLoad "%s".\nmain := external_value.\n' %
    str(outside / 'defs.v').replace('"', '""'))
env = dict(os.environ)
env.update(SOMA_CACHE=str(work / 'shared'), XDG_CACHE_HOME=str(work / 'xdg'),
           SOMA_OCAML_BUILD='0', SOMA_MIRAGE_BUILD='0')
for value in (1, 2):
    (outside / 'defs.v').write_text('Definition external_value : nat := %d.\n' % value)
    p = subprocess.run(['soma', 'build', 'main.soma'], cwd=root, env=env,
                       text=True, capture_output=True, timeout=90)
    assert p.returncode == 0, (p.stdout, p.stderr)
    p = subprocess.run(['soma', 'build', '--check-fresh', 'main.soma'], cwd=root, env=env,
                       text=True, capture_output=True, timeout=90)
    assert p.returncode != 0, ('external loaded objects were incorrectly certified', p.stdout, p.stderr)
print('actual external Load source remains uncertified for whole-build skipping: ok')
PY
