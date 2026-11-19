#!/usr/bin/env bash
# Toolchain keys use the complete driver identity, and source keys depend on
# relative source bytes rather than checkout locations or compiled outputs.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
python3 - <<'PY'
import os
import pathlib
import subprocess
import tempfile

with tempfile.TemporaryDirectory(prefix='soma-rocq-keys-') as tmp:
    outer = pathlib.Path(tmp).resolve()

    def project(name):
        root = outer / name
        lib = root / 'vendor/mylib'
        lib.mkdir(parents=True)
        (root / 'soma.toml').write_text('[project]\nname="keys"\nversion="0.1.0"\n')
        (lib / '_RocqProject').write_text('-Q . mylib\n')
        (lib / 'A.v').write_text('Definition value := 1.\n')
        (lib / 'B.v').write_text('From mylib Require Import A.\nDefinition twice := value + value.\n')
        (root / 'main.soma').write_text(
            'Rocq Library "mylib" in "vendor/mylib".\nFrom mylib Require Import B.\ntwice.\n')
        return root

    def build(root, identity='toolchain-one'):
        result = subprocess.run(['rocq', 'c', '-q', 'main.soma'], cwd=root,
                                env=dict(os.environ, SOMA_CACHE_ID=identity),
                                text=True, capture_output=True, timeout=60)
        assert result.returncode == 0, (root, result.stdout, result.stderr)
        return result

    def entries(root):
        return {f.parent.name for f in (root / '.soma-cache/rocq').glob('*/theories')}

    root = project('plain')
    build(root)
    first = entries(root)
    assert len(first) == 1, first
    build(root, 'toolchain-two')
    assert len(entries(root)) == 2, 'Rocq library reused after complete toolchain identity changed'

    for name in ['project with spaces', 'project\twith tab', 'project\nwith newline']:
        other = project(name)
        build(other)
        assert entries(other) == first, (first, entries(other))

    # A user compilation of the source checkout must not alter source identity.
    (root / 'vendor/mylib/A.vo').write_bytes(b'local compilation artifact')
    build(root)
    assert len(entries(root)) == 2, entries(root)
    (root / 'vendor/mylib/A.v').write_text('Definition value := 2.\n')
    result = build(root)
    assert 'Rocq: compiling ' in result.stderr, result.stderr
    assert len(entries(root)) == 3, entries(root)
print('Rocq toolchain identity, relative source keys and whitespace paths: passed')
PY
