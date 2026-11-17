#!/usr/bin/env bash
# Exercise real compiler dependency traces, not a second import parser.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
export SOMA_CACHE="$(mktemp -d)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP" "$SOMA_CACHE"' EXIT
export SOMA_TEST_FIXTURE="$TMP"
python3 - <<'PY'
import os
import pathlib
import subprocess
import time

outer = pathlib.Path(os.environ['SOMA_TEST_FIXTURE']).resolve()
subprocess.check_call(['git', 'init', '-q', str(outer)])
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

def selected(*args):
    return soma('--changedSince', 'baseline', '--listTests', *args).stdout.splitlines()

def expect(paths, *args):
    actual = selected(*args)
    assert actual == paths, (actual, paths)

git('config', 'user.name', 'Soma test')
git('config', 'user.email', 'test@example.invalid')
git('config', 'diff.relative', 'true')
put('.gitignore', '.soma-cache/\n')
put('soma.toml', '[project]\nname = "changed_tests"\nversion = "0.1.0"\n')
put('core/value.soma', 'value : nat := 2.\n')
put('bridge.soma', 'Import core.value.\nanswer := value.\n')
put('proof_only.soma', 'proof_value : nat := 1.\n')
put('bridge.exp', 'Import proof_only.\nTheorem answer_ok : answer = 2. Proof. reflexivity. Qed.\n')
put('spare.soma', 'spare : nat := 9.\n')
put('tests/a.soma', 'Import bridge.\na := answer.\n')
put('tests/a.exp', 'Theorem holds : a = 2. Proof. reflexivity. Qed.\n')
put('test/b.soma', 'b : nat := 7.\n')
git('add', '.')
git('commit', '-qm', 'baseline')
git('tag', 'baseline')
all_tests = ['test/b.soma', 'tests/a.soma']

# A cold list is read-only and includes tests without dependency records.
expect(all_tests)
assert not (root / '.soma-cache').exists()
start = time.monotonic()
soma()
full_seconds = time.monotonic() - start
start = time.monotonic()
expect([])
skip_seconds = time.monotonic() - start
expect(all_tests, '--no-image')  # a different build configuration

# An unrelated module does not select either test; transitive imports do.
put('spare.soma', 'spare : nat := 10.\n')
expect([])
put('core/value.soma', 'value : nat := 3.\n')
expect(['tests/a.soma'])
git('add', 'core/value.soma')
expect(['tests/a.soma'])  # staged changes
git('restore', '--staged', 'core/value.soma')
git('restore', 'core/value.soma', 'spare.soma')
expect([])
put('proof_only.soma', 'proof_value : nat := 2.\n')
expect(['tests/a.soma'])
git('restore', 'proof_only.soma')

# The same dependency must be retained when imported proofs are deferred.
os.environ['SOMA_DEFER_PROOFS'] = '1'
soma()
expect([])
put('proof_only.soma', 'proof_value : nat := 3.\n')
expect(['tests/a.soma'])
git('restore', 'proof_only.soma')
del os.environ['SOMA_DEFER_PROOFS']
soma()
expect([])

# Paired expectations are dependencies too; a failed check is not certified.
put('tests/a.exp', 'Theorem wrong : a = 3. Proof. reflexivity. Qed.\n')
expect(['tests/a.soma'])
assert soma('--changedSince', 'baseline', ok=False).returncode != 0
git('restore', 'tests/a.exp')
expect(['tests/a.soma'])  # previous failure removed its receipt
soma('--changedSince', 'baseline')
expect([])

# An added source may shadow a library: conservatively rebuild all tests.
put('new.soma', 'fresh : nat := 1.\n')
expect(all_tests)
(root / 'new.soma').unlink()
(root / 'core/value.soma').unlink()
expect(all_tests)  # deletion
git('restore', 'core/value.soma')

# Unknown resources, config, and extensions can affect arbitrary tests.
for path in ['resource.txt', 'rules.ext', 'soma.toml']:
    old = (root / path).read_text() if (root / path).exists() else None
    put(path, (old or '') + '\n')
    expect(all_tests)
    if old is None:
        (root / path).unlink()
    else:
        put(path, old)

# The compiler sees imports in .exp; comments and strings are not imports.
put('tests/a.exp', 'Import spare.\nTheorem holds : a = 2. Proof. reflexivity. Qed.\n')
put('test/b.soma', '(* Import spare. (* nested *) *)\nb := "Import spare.".\n')
soma()
git('add', '.')
git('commit', '-qm', 'expectation imports')
git('tag', '-f', 'baseline')
expect([])
put('spare.soma', 'spare : nat := 11.\n')
expect(['tests/a.soma'])
git('restore', 'spare.soma')

# Snapshot drift catches changes even when Git's chosen baseline has them.
put('core/value.soma', 'value : nat := 4.\n')
git('add', '.')
git('commit', '-qm', 'new baseline without rerunning tests')
assert soma('--changedSince', 'HEAD', '--listTests').stdout.splitlines() == ['tests/a.soma']
git('restore', '--source=baseline', 'core/value.soma')

# A corrupt record only widens selection. Invalid refs never run tests.
records = list((root / '.soma-cache/.tests').iterdir())
for record in records:
    record.write_text('garbage\n')
expect(all_tests)
assert soma('--changedSince', '--help', ok=False).returncode != 0
assert soma('--changedSince', 'does-not-exist', ok=False).returncode != 0

# Explicit scope, aliases, nested invocation, and option safety.
assert soma('tests', '--list-tests').stdout.splitlines() == ['tests/a.soma']
assert soma('--changed-since', 'baseline', '--list-tests', 'test').stdout.splitlines() == ['test/b.soma']
os.chdir(root / 'tests')
assert soma('--listTests', '.').stdout.splitlines() == ['tests/a.soma']
print('soma test changed selection: passed')
print(f'Fixture: full two-test run {full_seconds:.2f}s; unchanged selection {skip_seconds:.2f}s')
PY
