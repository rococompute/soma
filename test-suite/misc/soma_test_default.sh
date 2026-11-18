#!/usr/bin/env bash
# Default diff precedence using real compiler dependency receipts and local refs.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
export SOMA_CACHE="$(mktemp -d)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP" "$SOMA_CACHE"' EXIT
export SOMA_TEST_FIXTURE="$TMP"
python3 - <<'PY'
import os
from pathlib import Path
import subprocess

outer = Path(os.environ['SOMA_TEST_FIXTURE']).resolve()
subprocess.run(['git', 'init', '-q', '-b', 'main', str(outer)], check=True)
root = outer / 'project with spaces'
root.mkdir()
os.chdir(root)

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

def put(path, text):
    p = root / path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)

def soma(*args, ok=True):
    result = subprocess.run(['soma', 'test', *args], text=True, capture_output=True)
    if ok and result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return result

def expect(paths, *args):
    result = soma('--listTests', *args)
    assert result.stdout.splitlines() == paths, (result.stdout, result.stderr, paths)

git('config', 'user.name', 'Soma test')
git('config', 'user.email', 'test@example.invalid')
git('config', 'diff.relative', 'true')
put('.gitignore', '.soma-cache/\n')
put('soma.toml', '[project]\nname = "default_tests"\nversion = "0.1.0"\n')
put('a.soma', 'a : nat := 1.\n')
put('b.soma', 'b : nat := 2.\n')
put('unused.soma', 'unused : nat := 0.\n')
put('test/a.soma', 'Import a.\na_test := a.\n')
put('test/b.soma', 'Import b.\nb_test := b.\n')
git('add', '.')
git('commit', '-qm', 'baseline')
git('tag', 'baseline')
git('remote', 'add', 'origin', str(outer / 'nonexistent-remote'))
git('update-ref', 'refs/remotes/origin/main', 'HEAD')
git('symbolic-ref', 'refs/remotes/origin/HEAD', 'refs/remotes/origin/main')
git('switch', '-qc', 'feature')
git('update-ref', 'refs/remotes/origin/feature', 'HEAD')
git('branch', '--set-upstream-to=origin/feature')
all_tests = ['test/a.soma', 'test/b.soma']

# Cold selection remains conservative; --full creates real dependency records.
expect(all_tests)
assert not (root / '.soma-cache').exists()
soma('--full')
expect([])
expect(all_tests, '--full')

# Unstaged wins over staged. Receipt drift must not silently union the stages.
put('a.soma', 'a : nat := 3.\n')
git('add', 'a.soma')
put('b.soma', 'b : nat := 4.\n')
expect(['test/b.soma'])
expect(all_tests, '--changedSince', 'baseline')
expect(all_tests, '--full')
git('restore', 'b.soma')
expect(['test/a.soma'])
git('restore', '--staged', 'a.soma')
git('restore', 'a.soma')
expect([])

# Non-empty refers to the diff, not whether it happens to select any tests.
put('unused.soma', 'unused : nat := 5.\n')
put('a.soma', 'a : nat := 6.\n')
git('add', 'a.soma')
expect([])
git('restore', '--staged', 'a.soma')
git('restore', 'a.soma', 'unused.soma')

# Untracked inputs are unstaged. New/unknown inputs conservatively widen.
put('new.soma', 'new_value : nat := 1.\n')
expect(all_tests)
(root / 'new.soma').unlink()

# Remote branch comparison wins over default branch comparison.
put('a.soma', 'a : nat := 7.\n')
git('add', '.')
git('commit', '-qm', 'feature a')
git('update-ref', 'refs/remotes/origin/feature', 'HEAD')
put('b.soma', 'b : nat := 8.\n')
git('add', '.')
git('commit', '-qm', 'feature b')
expect(['test/b.soma'])
expect(all_tests, '--changedSince', 'baseline')
git('update-ref', 'refs/remotes/origin/feature', 'HEAD')
expect(all_tests)  # upstream is equal; now compare the default branch.
soma('--full')
expect(all_tests)  # baseline differences still matter after a passing run.

# Default-branch fallback works without an upstream, and from detached HEAD.
git('branch', '--unset-upstream')
git('update-ref', '-d', 'refs/remotes/origin/feature')
expect(all_tests)
git('switch', '--detach', '-q')
expect(all_tests)

# A stage outside this nested project must not hide the relevant later stage.
put('b.soma', 'b : nat := 9.\n')
git('add', 'b.soma')
(outer / 'outside.soma').write_text('outside : nat := 1.\n')
expect(['test/b.soma'])
(outer / 'outside.soma').unlink()
git('restore', '--staged', 'b.soma')
git('restore', 'b.soma')

# Explicit options are order independent; contradictory modes fail early.
for args in [('--full', '--changedSince', 'HEAD'), ('--changedSince', 'HEAD', '--full')]:
    assert soma(*args, ok=False).returncode == 2
assert soma('--changedSince', 'missing-ref', ok=False).returncode == 2
expect(['test/a.soma'], '--full', 'test/a.soma')
os.chdir(root / 'test')
expect(all_tests, '.')
print('soma test default waterfall: passed')
PY
