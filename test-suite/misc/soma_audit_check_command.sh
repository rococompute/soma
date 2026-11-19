#!/usr/bin/env bash

# First-class checking includes entry-point/imported proofs, but produces no
# automatic OCaml/Mirage products or false build-freshness receipts.
set -euo pipefail
export PATH="$BIN:$PATH"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
export SOMA_TEST_CHECK_COMMAND="$TMP"
export SOMA_CACHE="$TMP/shared"

python3 - <<'PY'
import os
import pathlib
import subprocess

tmp = pathlib.Path(os.environ['SOMA_TEST_CHECK_COMMAND']).resolve()
root = tmp / 'app'
root.mkdir()
(root / 'soma.toml').write_text('[project]\nname = "check_app"\nversion = "0.1.0"\n')
env = dict(os.environ)

def run(args, *, expected=0, extra=None):
    child_env = dict(env)
    if extra:
        child_env.update(extra)
    p = subprocess.run(['soma'] + args, cwd=root, env=child_env,
                       text=True, capture_output=True, timeout=90)
    assert (p.returncode == 0) == (expected == 0), (args, p.returncode, p.stdout, p.stderr)
    return p

help = run(['check', '--help'])
assert 'Usage: soma check FILE' in help.stdout, help.stdout
assert 'OCaml implementations' in help.stdout and 'not a source sandbox' in help.stdout
assert '  check ' in run(['help']).stdout
assert 'soma check: no file given' in run(['check'], expected=1).stderr

(root / 'plain.soma').write_text('value : nat := 1.\nvalue.\n')
(root / 'plain.exp').write_text('Theorem value_is : value = 1. Proof. reflexivity. Qed.\n')
run(['check', 'plain.soma'])
assert '= 1' in run(['check', '-v', 'plain.exp']).stdout
assert 'Chars ' in run(['check', 'plain.soma', '-time']).stdout
for flag in ('-vos', '-vok', '-o'):
    p = run(['check', 'plain.soma', flag, 'outside.vo'] if flag == '-o'
            else ['check', 'plain.soma', flag], expected=1)
    assert 'checks do not skip proofs or keep compiler outputs' in p.stderr, p.stderr
assert not (root / 'outside.vo').exists()

(root / 'bad.soma').write_text('value : nat := true.\n')
assert 'bool' in run(['check', 'bad.soma'], expected=1).stderr
(root / 'plain.exp').write_text('Theorem impossible : False. Proof. exact I. Qed.\n')
run(['check', 'plain.soma'], expected=1)
(root / 'plain.exp').write_text('Theorem value_is : value = 1. Proof. reflexivity. Qed.\n')

# Imported expectations cannot be bypassed by checking just the entry point.
(root / 'library.soma').write_text('n : nat := 1.\n')
(root / 'library.exp').write_text('Theorem impossible : False. Proof. exact I. Qed.\n')
(root / 'uses.soma').write_text('Import library.\nmain := n.\n')
run(['check', 'uses.soma'], expected=1, extra={'SOMA_DEFER_PROOFS': '1'})
(root / 'library.exp').unlink()
run(['check', 'uses.soma'])

# Fail-fast tool wrappers prove the automatic extraction/build path is not
# reached, even with build and explicit-export overrides inherited by the CLI.
tools = tmp / 'tools'
tools.mkdir()
calls = tmp / 'tool-calls'
for name in ('opam', 'dune', 'ocamlc'):
    tool = tools / name
    tool.write_text('#!/bin/sh\nprintf "%s\\n" "$0 $*" >> "$SOMA_TEST_CHECK_CALLS"\nexit 99\n')
    tool.chmod(0o755)
(root / 'native.ml').write_text('let message = "hello"\n')
(root / 'native.definition').write_text('message : string.\n')
(root / 'foreign.soma').write_text('Import native.\nmain : string := message.\n')
(root / 'sandbox.soma').write_text('Import Sandbox native.\nmain : io unit := print message.\n')
overrides = {'SOMA_OCAML_BUILD': '1', 'SOMA_MIRAGE_BUILD': '1',
             'SOMA_OCAML_EXTRACT': str(tmp / 'unwanted-export'),
             'SOMA_MIRAGE_DIR': str(tmp / 'unwanted-mirage'),
             'SOMA_MIRAGE_SWITCH': 'missing-check-only-switch',
             'SOMA_TEST_CHECK_CALLS': str(calls),
             'PATH': str(tools) + os.pathsep + env['PATH']}
run(['check', 'foreign.soma'], extra=overrides)
run(['check', 'sandbox.soma'], extra=overrides)
assert not calls.exists(), calls.read_text() if calls.exists() else ''
assert not (tmp / 'unwanted-export').exists()
assert not (tmp / 'unwanted-mirage').exists()
assert not list((root / '.soma-cache' / '.freshness').glob('*'))
for suffix in ('.vo', '.glob', '.exe', '.hvt', '.js', '.html'):
    assert not list(root.glob('*' + suffix)), (suffix, list(root.iterdir()))

# Explicit file-emitting extraction is also refused, before writing anything.
(root / 'explicit.soma').write_text(
    'Require Import Extraction.\nx : nat := 1.\nExtraction "forbidden" x.\n')
p = run(['check', 'explicit.soma'], expected=1)
assert 'not available in soma check' in p.stderr, p.stderr
assert not (root / 'forbidden.ml').exists()
assert not (root / 'forbidden.mli').exists()

# Choosing check in one process does not alter ordinary build/extract modes.
run(['build', 'plain.soma'])
run(['extract', 'foreign.soma', '-o', str(tmp / 'wanted-export')])
assert (tmp / 'wanted-export' / 'prog.ml').is_file()
print('soma check: types/proofs, no products, inherited overrides, writer refusal and normal build/extract: ok')
PY
