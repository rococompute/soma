#!/usr/bin/env bash
# A local Rocq library's original .v/config inputs participate in both
# import freshness and affected-test receipts, including imported consumers.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
python3 - <<'PY'
import os
import pathlib
import subprocess
import tempfile

with tempfile.TemporaryDirectory(prefix='soma-rocq-trace-') as tmp:
    root = pathlib.Path(tmp).resolve()
    (root / 'vendor').mkdir()
    (root / 'tests').mkdir()
    (root / 'soma.toml').write_text('[project]\nname="trace"\nversion="0.1.0"\n')
    (root / 'vendor/_RocqProject').write_text('-Q . mylib\n')
    (root / 'vendor/A.v').write_text('Definition from_library := 1.\n')
    (root / 'lib.soma').write_text(
        'Rocq Library "mylib" in "vendor".\nFrom mylib Require Import A.\nvalue := from_library.\n')
    (root / 'tests/main.soma').write_text('Import lib.\nvalue.\n')
    (root / 'tests/main.exp').write_text('Theorem checked : value = 1. Proof. reflexivity. Qed.\n')
    for args in [['init', '-q'], ['add', '.'], ['-c', 'user.name=Audit', '-c',
                 'user.email=audit@example.invalid', 'commit', '-qm', 'fixture']]:
        subprocess.run(['git', *args], cwd=root, check=True)
    env = dict(os.environ, SOMA_CACHE=str(root / 'shared'), XDG_CACHE_HOME=str(root / 'xdg'))

    def test(*args, expected=0):
        p = subprocess.run(['soma', 'test', *args], cwd=root, env=env,
                           text=True, capture_output=True, timeout=90)
        assert p.returncode == expected, (p.stdout, p.stderr)
        return p

    first = test('--full')
    assert 'next run will include' not in first.stderr, first.stderr
    assert test('--changedSince', 'HEAD', '--listTests').stdout == ''
    (root / 'vendor/A.v').write_text('Definition from_library := 2.\n')
    assert test('--changedSince', 'HEAD', '--listTests').stdout.strip() == 'tests/main.soma'
    # The new .v must actually be compiled, not just the test rerun against
    # the old imported consumer/cache. Its old expectation now fails.
    failed = subprocess.run(['soma', 'test', '--changedSince', 'HEAD'], cwd=root,
                            env=env, text=True, capture_output=True, timeout=90)
    assert failed.returncode != 0, (failed.stdout, failed.stderr)
    (root / 'tests/main.exp').write_text('Theorem checked : value = 2. Proof. reflexivity. Qed.\n')
    fixed = test('--changedSince', 'HEAD')
    assert 'next run will include' not in fixed.stderr, fixed.stderr
print('Rocq library source traces certify skips and invalidate stale imports: passed')
PY
