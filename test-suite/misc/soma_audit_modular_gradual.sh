#!/usr/bin/env bash
# E1: modular output must not silently split the gradual runtime across files.
# Shared output protects consumers and stays in the source project. The full
# emitted execution matrix lives in soma_audit_shared_gradual.sh.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
unset SOMA_EXPERIMENTAL_SHARED_EXTRACTION

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

    def shared(result, directory):
        assert result.returncode == 0, (result.stdout, result.stderr)
        assert (directory / 'soma_gradual_rt.ml').is_file(), list(directory.iterdir())
        outputs = [p for p in directory.glob('*.ml') if p.name != 'soma_gradual_rt.ml']
        assert outputs, list(directory.iterdir())
        assert all('module Gradual_rt = Soma_gradual_rt' in p.read_text() for p in outputs), outputs

    project = root / "project"
    project.mkdir()
    (project / "soma.toml").write_text(
        '[project]\nname = "modular_gradual"\nversion = "0.1.0"\n')
    source = project / "main.soma"
    source.write_text(prelude + "Definition unknown_nat : nat := unk.\n"
                      "Separate Extraction unknown_nat.\n")
    shared(run(["soma", "build", str(source)], root), project)
    assert not list(root.glob("*.ml*")), list(root.iterdir())

    # A match can require the gradual runtime even without explicit casts or
    # unknown terms: it must propagate unknown values supplied by a caller.
    source.write_text(prelude +
                      "Definition predecessor (n : nat) := match n with O => 0 | S k => k end.\n"
                      "Separate Extraction predecessor.\n")
    shared(run(["soma", "build", str(source)], root), project)
    assert any('Gradual_rt.propagate' in p.read_text() or 'Gradual_rt.check' in p.read_text()
               for p in project.glob('*.ml') if p.name != 'soma_gradual_rt.ml')
    assert not list(root.glob("*.ml*")), list(root.iterdir())

    # Both library commands use the same shared output, including a library
    # whose consumer has no casts of its own. Raw Rocq files avoid Soma's
    # separate restrictions on dependency file effects.
    raw = root / "raw"
    raw.mkdir()
    (raw / "Producer.v").write_text(prelude + "Definition unknown_nat : nat := unk.\n")
    result = run(["rocq", "c", "-q", "Producer.v"], raw)
    assert result.returncode == 0, (result.stdout, result.stderr)
    (raw / "Consumer.v").write_text("Require Import Producer.\nDefinition consume := S unknown_nat.\n")
    result = run(["rocq", "c", "-q", "Consumer.v"], raw)
    assert result.returncode == 0, (result.stdout, result.stderr)
    for index, command in enumerate(("Extraction Library Producer.",
                                     "Recursive Extraction Library Producer.",
                                     "Separate Extraction Consumer.consume.",
                                     "Extraction Library Consumer.",
                                     "Recursive Extraction Library Consumer.")):
        request = raw / ("Request%d.v" % index)
        request.write_text("Require Import Consumer.\nFrom Corelib Require Extraction.\n" + command + "\n")
        shared(run(["rocq", "c", "-q", request.name], raw), raw)

    # The supported one-file path still emits the runtime and guards.
    source.write_text(prelude + "Definition unknown_nat : nat := unk.\n"
                      'Extraction "one_file" unknown_nat.\n')
    result = run(["soma", "build", str(source)], root)
    assert result.returncode == 0, (result.stdout, result.stderr)
    output = (project / "one_file.ml").read_text()
    assert "module Gradual_rt = struct" in output
    assert "Gradual_rt.unknown_term" in output
    assert not (root / "one_file.ml").exists()

print("default modular gradual extraction shares a confined runtime; monolithic extraction works: ok")
PY
