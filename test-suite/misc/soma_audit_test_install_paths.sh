#!/usr/bin/env bash
# Test subprocesses must inherit the same resolved library installation as
# their parent, without requiring developers to export ROCQLIB manually.
set -euo pipefail
export PATH="$BIN:$PATH"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
export SOMA_TEST_INSTALL_PATHS="$TMP"
python3 - <<'PY'
import os
import pathlib
import shutil
import subprocess

tmp = pathlib.Path(os.environ['SOMA_TEST_INSTALL_PATHS']).resolve()
(tmp / 'tests').mkdir()
(tmp / 'soma.toml').write_text('[project]\nname = "paths"\nversion = "0.1.0"\n')
(tmp / 'tests' / 'simple.soma').write_text('value : nat := 1.\n')
(tmp / 'tests' / 'simple.exp').write_text(
    'Theorem value_is : value = 1. Proof. reflexivity. Qed.\n')
env = dict(os.environ)
for name in ('ROCQLIB', 'ROCQRUNTIMELIB', 'COQLIB', 'COQCORELIB', 'OCAMLPATH'):
    env.pop(name, None)
env.update(SOMA_CACHE=str(tmp / 'shared'), XDG_CACHE_HOME=str(tmp / 'xdg'),
           SOMA_MIRAGE_BUILD='0', SOMA_OCAML_BUILD='0')
binary = shutil.which('soma')
assert binary
for args in (['build', 'tests/simple.soma'], ['test', '--full']):
    p = subprocess.run([binary] + args, cwd=tmp, env=env,
                       text=True, capture_output=True, timeout=90)
    assert p.returncode == 0, (args, p.stdout, p.stderr)
    assert 'Prelude.vo' not in p.stderr, p.stderr
print('test child resolves the parent installation without ROCQLIB: ok')
PY
