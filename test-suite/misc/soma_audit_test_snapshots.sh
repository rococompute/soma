#!/usr/bin/env bash
# Snapshot symlink fixtures and opaque Git submodules without certifying
# untraced submodule/external sources. --full needs no Git checkout.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
TMP="$(mktemp -d)"
export SOMA_CACHE="$TMP/store"
export SOMA_TEST_FIXTURE="$TMP"
trap 'rm -rf "$TMP"' EXIT
python3 - <<'PY'
import os
from pathlib import Path
import subprocess

outer = Path(os.environ['SOMA_TEST_FIXTURE']).resolve()
root = outer / 'project with spaces'
root.mkdir()
os.chdir(root)

def git(*args, cwd=root):
    return subprocess.check_output(['git', '-C', str(cwd), *args], text=True).strip()

def put(name, text):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)

def soma(*args, ok=True, cwd=root):
    result = subprocess.run(['soma', 'test', *args], cwd=cwd, text=True,
                            capture_output=True, timeout=120)
    if ok:
        assert result.returncode == 0, (args, result.stdout, result.stderr)
    return result

def selected(*args):
    return soma('--listTests', *args).stdout.splitlines()

git('init', '-q')
git('config', 'user.name', 'Soma snapshot test')
git('config', 'user.email', 'test@example.invalid')
git('config', 'advice.addEmbeddedRepo', 'false')
put('.gitignore', '.soma-cache/\n')
put('soma.toml', '[project]\nname = "snapshot_tests"\nversion = "0.1.0"\n')
put('tests/main.soma', 'main : nat := 1.\n')
put('shared/alias.soma', 'alias_value : nat := 2.\n')
put('shared/alias.exp', 'Theorem target_only : alias_value = 999. Proof. reflexivity. Qed.\n')
put('tests/internal.exp', 'Theorem alias_only : alias_value = 2. Proof. reflexivity. Qed.\n')
(root / 'tests/internal.soma').symlink_to('../shared/alias.soma')
(root / 'tests/cycle').symlink_to('.')
(root / 'tests/external-data.txt').symlink_to(outer / 'external-data')
(root / 'external-fixture').symlink_to(outer / 'external-data')
(outer / 'external-data').write_text('private fixture bytes\n')
(root / 'broken-fixture').symlink_to('absent')
(root / 'cyclic-fixture').symlink_to('cyclic-fixture')

# A gitlink has no per-source entries in the parent's Git listing.
vendor = root / 'vendor'
vendor.mkdir()
git('init', '-q', cwd=vendor)
git('config', 'user.name', 'Soma snapshot test', cwd=vendor)
git('config', 'user.email', 'test@example.invalid', cwd=vendor)
put('vendor/value.soma', 'submodule_value : nat := 3.\n')
git('add', '.', cwd=vendor)
git('commit', '-qm', 'submodule', cwd=vendor)
git('add', '.')
git('commit', '-qm', 'snapshot fixture')
all_tests = ['tests/internal.soma', 'tests/main.soma']
assert selected('--full') == all_tests
soma('--full')
assert selected('--changedSince', 'HEAD') == []

# The alias's own expectations run; the target's deliberately wrong .exp
# is not substituted. A failing alias-local expectation must fail the run.
put('tests/internal.exp', 'Theorem alias_wrong : alias_value = 999. Proof. reflexivity. Qed.\n')
assert soma('--full', ok=False).returncode != 0
put('tests/internal.exp', 'Theorem alias_only : alias_value = 2. Proof. reflexivity. Qed.\n')
soma('--full')

# Editing the actual target selects the lexical alias in both explicit and
# automatic diff modes, without relying solely on receipt-drift selection.
put('shared/alias.soma', 'alias_value : nat := 4.\n')
assert selected('--changedSince', 'HEAD') == ['tests/internal.soma']
assert selected() == ['tests/internal.soma']
git('restore', 'shared/alias.soma')
put('shared/alias.exp', 'Theorem other_target_only : alias_value = 998. Proof. reflexivity. Qed.\n')
assert selected() == []  # target-local expectations are not alias companions
git('restore', 'shared/alias.exp')

# External fixture bytes are not read merely to snapshot the project.
(outer / 'external-data').write_text('different external bytes\n')
assert selected('--changedSince', 'HEAD') == []

# Sources imported from gitlinks remain uncertified and always rerun.
put('tests/submodule.soma', 'Import vendor.value.\nfrom_submodule := submodule_value.\n')
git('add', 'tests/submodule.soma')
git('commit', '-qm', 'import submodule')
result = soma('--full')
assert 'dependency is not tracked by Git discovery' in result.stderr, result.stderr
assert selected('--changedSince', 'HEAD') == ['tests/submodule.soma']
put('vendor/value.soma', 'submodule_value : nat := 5.\n')
assert selected('--changedSince', 'HEAD') == all_tests + ['tests/submodule.soma']

# Ignored alias targets are not visible to Git's default diff, so those
# tests must remain uncertified even though the alias itself is tracked.
git('restore', 'value.soma', cwd=vendor)
put('.gitignore', '.soma-cache/\nshared/ignored.soma\n')
put('shared/ignored.soma', 'ignored_value : nat := 7.\n')
(root / 'tests/ignored.soma').symlink_to('../shared/ignored.soma')
git('add', '.gitignore', 'tests/ignored.soma')
git('commit', '-qm', 'ignored alias target')
soma('--full')
assert selected('--changedSince', 'HEAD') == ['tests/ignored.soma', 'tests/submodule.soma']
assert selected() == ['tests/ignored.soma', 'tests/submodule.soma']

# Explicit test aliases may not escape or hide a missing .soma target.
escape = outer / 'escape.soma'
escape.write_text('escape : nat := 1.\n')
(root / 'tests/escape.soma').symlink_to(escape)
result = soma('--full', ok=False)
assert result.returncode != 0 and 'outside the project' in result.stderr, result.stderr
(root / 'tests/escape.soma').unlink()
(root / 'tests/missing.soma').symlink_to('absent.soma')
result = soma('--full', ok=False)
assert result.returncode != 0 and 'cannot resolve test path' in result.stderr, result.stderr
(root / 'tests/missing.soma').unlink()

# --full works in unpacked source without any Git repository.
unpacked = outer / 'unpacked'
(unpacked / 'test').mkdir(parents=True)
(unpacked / 'soma.toml').write_text('[project]\nname = "unpacked"\nversion = "0.1.0"\n')
(unpacked / 'test/plain.soma').write_text('plain : nat := 6.\n')
assert soma('--full', '--listTests', cwd=unpacked).stdout.splitlines() == ['test/plain.soma']
result = soma('--full', cwd=unpacked)
assert 'not a git repository' not in result.stderr, result.stderr
result = soma('--listTests', cwd=unpacked, ok=False)
assert result.returncode != 0 and 'use --full' in result.stderr, result.stderr
print('soma test snapshots, symlinks, opaque submodules and non-Git --full: passed')
PY
