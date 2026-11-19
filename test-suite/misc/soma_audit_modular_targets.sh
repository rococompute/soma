#!/usr/bin/env bash
# E2: modular extraction from another cwd writes only inside its source
# project. Validate existing implementation/signature symlinks before output.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0

python3 - <<'PY'
import os
import pathlib
import subprocess
import tempfile

with tempfile.TemporaryDirectory(prefix="soma-modular-targets-") as tmp:
    outer = pathlib.Path(tmp).resolve()
    caller = outer / "caller"
    caller.mkdir()
    (caller / "main.ml").write_text("caller sentinel\n")
    env = dict(os.environ, SOMA_CACHE=str(outer / "cache"))
    serial = 0

    def project():
        global serial
        serial += 1
        root = outer / ("project%d" % serial)
        root.mkdir()
        (root / "soma.toml").write_text(
            '[project]\nname = "modular_targets"\nversion = "0.1.0"\n')
        return root

    def build(root, command="Separate Extraction x.", setting=None):
        source = root / "main.soma"
        output = ('Set Extraction Output Directory "%s".\n' % setting) if setting else ""
        source.write_text("From Corelib Require Extraction.\nDefinition x := 1.\n" + output + command + "\n")
        return subprocess.run(["soma", "build", str(source)], cwd=caller,
                              env=env, text=True, capture_output=True, timeout=60)

    def success(result):
        assert result.returncode == 0, (result.stdout, result.stderr)
        assert (caller / "main.ml").read_text() == "caller sentinel\n"
        assert not list(caller.glob("*.mli")), list(caller.iterdir())

    def refused(result):
        assert result.returncode != 0, (result.stdout, result.stderr)
        assert "must stay inside the project being built" in result.stderr, result.stderr
        assert (caller / "main.ml").read_text() == "caller sentinel\n"

    root = project()
    success(build(root))
    assert (root / "main.ml").is_file()
    assert (root / "main.mli").is_file()
    assert (root / "Datatypes.ml").is_file()

    for command in ("Extraction Library Datatypes.",
                    "Recursive Extraction Library Datatypes."):
        root = project()
        success(build(root, command))
        assert (root / "Datatypes.ml").is_file()
        assert (root / "Datatypes.mli").is_file()

    for absolute in (False, True):
        root = project()
        directory = root / "generated"
        success(build(root, setting=str(directory) if absolute else "generated"))
        assert (directory / "main.ml").is_file()
        assert not (caller / "generated").exists()

    # Bad output-directory settings must not even create their destination.
    for setting in ("../escape-relative", str(outer / "escape-absolute")):
        root = project()
        refused(build(root, setting=setting))
    assert not (outer / "escape-relative").exists()
    assert not (outer / "escape-absolute").exists()

    outside = outer / "outside"
    outside.mkdir()
    for suffix in (".ml", ".mli"):
        root = project()
        victim = outside / ("victim" + suffix)
        victim.write_text("outside sentinel\n")
        (root / ("main" + suffix)).symlink_to(victim)
        refused(build(root))
        assert victim.read_text() == "outside sentinel\n"
        # Both names are validated before the implementation is opened.
        if suffix == ".mli":
            assert not (root / "main.ml").exists()

    root = project()
    (root / "generated").symlink_to(outside, target_is_directory=True)
    refused(build(root, setting="generated"))
    assert not (outside / "main.ml").exists()
    root = project()
    (root / "main.ml").symlink_to(outside / "missing.ml")
    refused(build(root))
    assert not (outside / "missing.ml").exists()

    # Existing explicit monolithic targets use the same confinement helper.
    root = project()
    success(build(root, 'Extraction "one" x.'))
    assert (root / "one.ml").is_file()

print("modular extraction is project-rooted and refuses outside/symlink targets: ok")
PY
