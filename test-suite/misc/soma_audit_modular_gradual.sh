#!/usr/bin/env bash
# E1: modular output must not silently split the gradual runtime across files.
# Until a shared runtime/guard ABI exists, refuse the entire output before any
# dependency file is emitted, while retaining monolithic gradual extraction.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0

python3 - <<'PY'
import os
import pathlib
import subprocess
import tempfile

with tempfile.TemporaryDirectory(prefix="soma-modular-gradual-") as tmp:
    root = pathlib.Path(tmp).resolve()
    env = dict(os.environ, SOMA_CACHE=str(root / "cache"))
    prelude = ("From Corelib.Gradual Require Import Gradual.\n"
               "From Corelib Require Extraction.\n")

    def run(args, cwd):
        return subprocess.run(args, cwd=cwd, env=env, text=True,
                              capture_output=True, timeout=60)

    def refused(result):
        assert result.returncode != 0, (result.stdout, result.stderr)
        assert "Modular extraction of gradual code is not supported" in result.stderr, result.stderr
        assert 'Extraction "file"' in result.stderr, result.stderr

    project = root / "project"
    project.mkdir()
    (project / "soma.toml").write_text(
        '[project]\nname = "modular_gradual"\nversion = "0.1.0"\n')
    source = project / "main.soma"
    source.write_text(prelude + "Definition unknown_nat : nat := unk.\n"
                      "Separate Extraction unknown_nat.\n")
    refused(run(["soma", "build", str(source)], root))
    assert not list(project.glob("*.ml*")), list(project.iterdir())
    assert not list(root.glob("*.ml*")), list(root.iterdir())

    # Both library commands use the same preflight, including a library whose
    # consumer has no casts of its own. These are raw Rocq files so refusing
    # dependency effects in Soma cannot mask the modular-runtime check.
    raw = root / "raw"
    raw.mkdir()
    (raw / "Producer.v").write_text(prelude + "Definition unknown_nat : nat := unk.\n")
    result = run(["rocq", "c", "-q", "Producer.v"], raw)
    assert result.returncode == 0, (result.stdout, result.stderr)
    for index, command in enumerate(("Extraction Library Producer.",
                                     "Recursive Extraction Library Producer.")):
        consumer = raw / ("Consumer%d.v" % index)
        consumer.write_text("Require Import Producer.\nFrom Corelib Require Extraction.\n" + command + "\n")
        refused(run(["rocq", "c", "-q", consumer.name], raw))
        assert not list(raw.glob("*.ml*")), list(raw.iterdir())

    # The supported one-file path still emits the runtime and guards.
    source.write_text(prelude + "Definition unknown_nat : nat := unk.\n"
                      'Extraction "one_file" unknown_nat.\n')
    result = run(["soma", "build", str(source)], root)
    assert result.returncode == 0, (result.stdout, result.stderr)
    output = (project / "one_file.ml").read_text()
    assert "module Gradual_rt = struct" in output
    assert "Gradual_rt.unknown_term" in output
    assert not (root / "one_file.ml").exists()

print("modular gradual extraction is refused before output; monolithic extraction works: ok")
PY
