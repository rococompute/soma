#!/usr/bin/env bash
# The check-only worker must reject explicit file-generating extraction
# commands before filenames/destination directories or temporary files exist.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0

python3 - <<'PY'
import os
import pathlib
import subprocess
import tempfile

with tempfile.TemporaryDirectory(prefix="soma-check-extraction-") as tmp:
    outer = pathlib.Path(tmp).resolve()
    commands = ['Extraction "out" x.', 'Separate Extraction x.',
                'Extraction Library Datatypes.', 'Recursive Extraction Library Datatypes.',
                'Extraction TestCompile x.']
    env = dict(os.environ, SOMA_CHECK_ONLY="1", SOMA_CACHE=str(outer / "cache"))
    prelude = "From Corelib Require Extraction.\nDefinition x := 1.\n"
    for index, command in enumerate(commands):
        root = outer / ("case%d" % index)
        root.mkdir()
        (root / "main.soma").write_text(prelude + command + "\n")
        result = subprocess.run(["soma", "build", "main.soma"], cwd=root,
                                env=env, text=True, capture_output=True, timeout=60)
        assert result.returncode != 0, (command, result.stdout, result.stderr)
        assert "not available in soma check" in result.stderr, (command, result.stderr)
        assert "use soma build or soma extract" in result.stderr, (command, result.stderr)
        assert not list(root.glob("*.ml*")), list(root.iterdir())

    # Pure, explicitly requested stdout inspection remains usable, and the
    # setting itself cannot create its destination directory.
    root = outer / "stdout"
    root.mkdir()
    (root / "main.soma").write_text(prelude +
        'Set Extraction Output Directory "not_created".\nRecursive Extraction x.\n')
    result = subprocess.run(["soma", "build", "main.soma"], cwd=root,
                            env=env, text=True, capture_output=True, timeout=60)
    assert result.returncode == 0, (result.stdout, result.stderr)
    assert not (root / "not_created").exists()
    assert not list(root.glob("*.ml*")), list(root.iterdir())

print("check-only extraction writer guards and stdout inspection: ok")
PY
