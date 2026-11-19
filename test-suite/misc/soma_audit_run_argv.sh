#!/usr/bin/env bash

# Compile real Sandbox source with stand-in external build/run tools. The
# temporary output path deliberately contains shell punctuation and spaces;
# argv transport must preserve it, and user arguments, as literal bytes.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
export SOMA_TEST_RUN_ARGV="$WORK"
python3 - <<'PY'
import json
import os
import pathlib
import subprocess

work = pathlib.Path(os.environ['SOMA_TEST_RUN_ARGV']).resolve()
fake = work / 'fake'
fake.mkdir()
scripts = {
    'opam': '''#!/bin/sh
case "$1" in
  exec) shift; while [ "$1" != -- ]; do shift; done; shift; exec "$@" ;;
  var) printf 'fake\\n' ;;
  --version) printf '2.3.0\\n' ;;
  repo) printf 'default\\n' ;;
  monorepo) exit 0 ;;
  *) exit 2 ;;
esac
''',
    'mirage': '#!/bin/sh\nexit 0\n',
    'make': '#!/bin/sh\nif [ "$1" = build ]; then mkdir -p dist; : > dist/soma.hvt; fi\n',
    'solo5-vmnet': '#!/bin/sh\n[ "$1" = -- ] || exit 2\nshift\nexec "$@"\n',
    'solo5-hvt': '''#!/usr/bin/env python3
import json, os, pathlib, sys
args = sys.argv[1:]
separator = args.index('--')
image = args[separator + 1]
assert pathlib.Path(image).is_file(), ('image argument was split', args)
pathlib.Path(os.environ['SOMA_TEST_RUN_RESULT']).write_text(json.dumps(args))
print('image argv preserved')
''',
}
for name, contents in scripts.items():
    p = fake / name
    p.write_text(contents)
    p.chmod(0o755)
source = work / 'app'
source.mkdir()
(source / 'main.soma').write_text('Require Import Sandbox.\nmain := print "hello".\n')
temp = work / "temporary space, 'quote; $literal"
temp.mkdir()
result = work / 'argv.json'
env = dict(os.environ)
env.update(PATH=str(fake) + os.pathsep + env['PATH'], TMPDIR=str(temp),
           SOMA_TEST_RUN_RESULT=str(result), SOMA_MIRAGE_SWITCH='fake',
           SOMA_MIRAGE_DIR=str(work / 'mirage'), SOMA_CACHE=str(work / 'cache'))
env.pop('SOMA_MIRAGE_BUILD', None)
env.pop('SOMA_MIRAGE_NO_IMAGE', None)
arguments = ['user argument with spaces', "quote'and;literal", '', '$(touch should-not-exist)']
p = subprocess.run(['soma', 'run', 'main.soma', '--'] + arguments,
                   cwd=source, env=env, capture_output=True, text=True, timeout=120)
assert p.returncode == 0, (p.stdout, p.stderr)
assert 'image argv preserved' in p.stdout, p.stdout
args = json.loads(result.read_text())
separator = args.index('--')
assert str(temp) in args[separator + 1], args
assert args[separator + 2:] == arguments, args
assert not (source / 'should-not-exist').exists()
assert not list(temp.iterdir()), 'soma run did not clean its temporary compilation'
print('Mirage runner preserves image paths and user argv without shell splitting: ok')
PY
