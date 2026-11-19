#!/usr/bin/env bash

# A completed Rocq cache entry can still be in a live REPL's load path.
# Compiling a different source key of that package must not remove it.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0

python3 - <<'PY'
import os
import pathlib
import re
import subprocess
import tempfile
import time

with tempfile.TemporaryDirectory(prefix="soma-rocq-lifetime-") as tmp:
    root = pathlib.Path(tmp).resolve()
    (root / "soma.toml").write_text(
        '[project]\nname = "lifetime"\nversion = "0.1.0"\n')
    for key, value in [("a", 1), ("b", 2)]:
        lib = root / "vendor" / key
        lib.mkdir(parents=True)
        (lib / "_RocqProject").write_text("-Q . mylib\n")
        (lib / "A.v").write_text("Definition audit_value := %d.\n" % value)
        (root / (key + ".soma")).write_text(
            'Rocq Library "mylib" in "vendor/%s".\n' % key)
    env = dict(os.environ, SOMA_CACHE=str(root / "store"),
               XDG_CACHE_HOME=str(root / "xdg"))
    log = root / "repl.log"
    with log.open("w") as out:
        repl = subprocess.Popen(["soma", "repl", "a.soma"], cwd=root, env=env,
                                stdin=subprocess.PIPE, stdout=out,
                                stderr=subprocess.STDOUT, text=True)
        try:
            # The library has finished compiling and its lock is released,
            # but the REPL has not yet loaded A.vo from that library.
            repl.stdin.write("Check nat.\n")
            repl.stdin.flush()
            deadline = time.monotonic() + 60
            while not re.search(r"nat\s+: Set", log.read_text()):
                assert repl.poll() is None, log.read_text()
                assert time.monotonic() < deadline, log.read_text()
                time.sleep(0.02)
            previous = list((root / ".soma-cache" / "rocq").glob("*/theories"))
            assert len(previous) == 1, previous
            old_entry = previous[0].parent

            other = subprocess.run(["soma", "build", "b.soma"], cwd=root,
                                   env=env, text=True, capture_output=True, timeout=60)
            assert other.returncode == 0, (other.stdout, other.stderr)
            assert "Rocq: compiling " in other.stderr, other.stderr
            repl.stdin.write(
                "From mylib Require Import A.\nEval compute in audit_value.\nQuit.\n")
            repl.stdin.flush()
            assert repl.wait(timeout=30) == 0, log.read_text()
            output = log.read_text()
            assert "Error:" not in output, output
            assert re.search(r"=\s*1\s*: nat", output), output
            assert old_entry.is_dir(), "the live REPL's library was removed"
            assert len(list((root / ".soma-cache" / "rocq").glob("*/theories"))) == 2
        finally:
            if repl.poll() is None:
                repl.kill()
                repl.wait()
print("soma audit: completed Rocq entries outlive compilation locks: passed")
PY
