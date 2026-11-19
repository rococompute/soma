#!/usr/bin/env bash
# Native project filenames cannot shadow each other or a declared library top.
# An apostrophe, contrary to the original audit claim, is legal in OCaml names.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_OCAML_BUILD=0 SOMA_MIRAGE_BUILD=0
python3 - <<'PY'
import os, pathlib, subprocess, tempfile
with tempfile.TemporaryDirectory(prefix="soma-ocaml-names-") as tmp:
    outer = pathlib.Path(tmp).resolve()
    env = dict(os.environ, SOMA_CACHE=str(outer / "cache"))
    def case(name, first, second, library=False):
        root = outer / name
        root.mkdir()
        for directory, module in (("left", first), ("right", second)):
            folder = root / directory
            folder.mkdir()
            if directory != "right" or not library:
                (folder / (module + ".ml")).write_text("let value = 1\n")
            (folder / (module + ".definition")).write_text(
                ('OCaml Library "unix".\n' if directory == "right" and library else '') +
                "value : nat.\n")
        (root / "main.soma").write_text(
            "Import left.%s right.%s.\nmain := left.%s.value + right.%s.value.\n" %
            (first, second, first, second))
        result = subprocess.run(["soma", "extract", "main.soma", "-o", "out"],
                                cwd=root, env=env, text=True, capture_output=True, timeout=60)
        assert result.returncode != 0, (name, result.stdout, result.stderr)
        diagnostic = " ".join(result.stderr.split())
        expected = "shadows a library module" if library else "two OCaml modules named"
        assert expected in diagnostic, (name, diagnostic)
        assert not (root / "out").exists(), name
    case("casefold", "foo", "fOO")
    case("library", "foo", "foo", library=True)
    root = outer / "apostrophe"
    root.mkdir()
    (root / "foo'.ml").write_text("let value = 1\n")
    (root / "foo'.definition").write_text("value : nat.\n")
    (root / "main.soma").write_text("Import foo'.\nmain := foo'.value.\n")
    result = subprocess.run(["soma", "extract", "main.soma", "-o", "out"],
                            cwd=root, env=env, text=True, capture_output=True, timeout=60)
    assert result.returncode == 0, (result.stdout, result.stderr)
    assert (root / "out" / "foo'.ml").read_text().endswith("let value = 1\n")
print("native module collisions rejected; legal apostrophe retained: ok")
PY
