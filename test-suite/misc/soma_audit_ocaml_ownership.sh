#!/usr/bin/env bash
# Re-export may remove only unchanged obsolete generated modules. Files added
# or edited by the user survive, and are excluded from dune's module list.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_OCAML_BUILD=0 SOMA_MIRAGE_BUILD=0
python3 - <<'PY'
import fcntl, os, pathlib, subprocess, tempfile, time
with tempfile.TemporaryDirectory(prefix="soma-ocaml-ownership-") as tmp:
    root = pathlib.Path(tmp).resolve()
    env = dict(os.environ, SOMA_CACHE=str(root / "cache"))
    for name in ("foo", "bar"):
        (root / (name + ".ml")).write_text("let value = 1\n")
        (root / (name + ".definition")).write_text("value : nat.\n")
    source = root / "main.soma"
    source.write_text("Import foo bar.\nmain := foo.value + bar.value.\n")
    command = ["soma", "extract", "main.soma", "-o", "out"]
    def export():
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                capture_output=True, timeout=60)
        assert result.returncode == 0, (result.stdout, result.stderr)
    export()
    out = root / "out"
    assert (out / "foo.ml").exists() and (out / "bar.ml").exists()
    (out / "foo.ml").write_text("user-edited obsolete module\n")
    (out / "user_notes.ml").write_text("unrelated user file\n")
    (out / "user_notes.mli").write_text("unrelated signature\n")
    source.write_text("main : nat := 1.\n")
    export()
    assert (out / "foo.ml").read_text() == "user-edited obsolete module\n"
    assert not (out / "bar.ml").exists(), "unchanged obsolete module was kept"
    assert (out / "user_notes.ml").read_text() == "unrelated user file\n"
    assert (out / "user_notes.mli").read_text() == "unrelated signature\n"
    dune = (out / "dune").read_text()
    assert "(modules " in dune
    for name in ("Foo", "Bar", "User_notes"):
        assert '"' + name + '"' not in dune, dune
    # Hold the production lock across a warm export. The worker must wait,
    # then finish after release; the lock is outside the directory it manages.
    lock = root / ".out.soma-ocaml.lock"
    with lock.open("a+") as handle:
        fcntl.lockf(handle.fileno(), fcntl.LOCK_EX)
        proc = subprocess.Popen(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            time.sleep(1)
            assert proc.poll() is None, "export did not wait for the directory lock"
            fcntl.lockf(handle.fileno(), fcntl.LOCK_UN)
            stdout, stderr = proc.communicate(timeout=60)
            assert proc.returncode == 0, (stdout, stderr)
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.communicate()
print("generated-file ownership, explicit dune modules and export lock: ok")
PY
