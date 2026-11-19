#!/usr/bin/env bash
# E4: a file passed as -o gets a useful diagnostic and is never overwritten.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0

python3 - <<'PY'
import os
import pathlib
import subprocess
import tempfile

with tempfile.TemporaryDirectory(prefix="soma-extract-destination-") as tmp:
    root = pathlib.Path(tmp).resolve()
    (root / "main.soma").write_text("main : nat := 1.\n")
    env = dict(os.environ, SOMA_CACHE=str(root / "cache"))
    for name, content in (("empty", ""), ("with space", "sentinel\n")):
        output = root / name
        output.write_text(content)
        result = subprocess.run(["soma", "extract", "main.soma", "-o", str(output)],
                                cwd=root, env=env, text=True, capture_output=True, timeout=60)
        assert result.returncode != 0, (result.stdout, result.stderr)
        assert "is not a directory" in result.stderr, result.stderr
        assert "extract into a new directory (-o DIR)" in result.stderr, result.stderr
        assert "System error" not in result.stderr, result.stderr
        assert output.read_text() == content

print("extract rejects a file destination with an actionable diagnostic: ok")
PY
