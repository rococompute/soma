#!/usr/bin/env bash
# A build with the explicit export override must not masquerade as a pure
# successful check: the export is a requested product outside the source tree.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
export SOMA_TEST_EXPORT_FRESHNESS="$WORK"
python3 - <<'PY'
import os
import pathlib
import shutil
import subprocess

work = pathlib.Path(os.environ['SOMA_TEST_EXPORT_FRESHNESS']).resolve()
root = work / 'app'
root.mkdir()
(root / 'soma.toml').write_text('[project]\nname = "export_app"\nversion = "0.1.0"\n')
(root / 'helper.soma').write_text('message : string := "hello".\n')
(root / 'main.soma').write_text('Import helper.\nmain : string := message.\n')
out = work / 'export'
env = dict(os.environ)
env.update(SOMA_CACHE=str(work / 'shared'), XDG_CACHE_HOME=str(work / 'xdg'),
           SOMA_OCAML_BUILD='0', SOMA_MIRAGE_BUILD='0', SOMA_OCAML_EXTRACT=str(out))
def run(args):
    return subprocess.run(['soma'] + args, cwd=root, env=env,
                          text=True, capture_output=True, timeout=90)
for _ in range(2):
    p = run(['build', 'main.soma'])
    assert p.returncode == 0, (p.stdout, p.stderr)
    assert (out / 'prog.ml').is_file()
    shutil.rmtree(out)
    p = run(['build', '--check-fresh', 'main.soma'])
    assert p.returncode != 0, ('an explicit export was certified without its outputs', p.stdout, p.stderr)
print('explicit export overrides always regenerate requested outputs: ok')
PY
