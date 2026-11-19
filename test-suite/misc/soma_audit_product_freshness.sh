#!/usr/bin/env bash

# Real kernel/extraction stages, stand-in external image build: unidentified
# foreign tool/SDK closures must remain non-fresh even when products exist.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
export SOMA_TEST_PRODUCT_FRESHNESS="$WORK"
python3 - <<'PY'
import os
import pathlib
import subprocess
import time

work = pathlib.Path(os.environ['SOMA_TEST_PRODUCT_FRESHNESS']).resolve()
root, fake, prefix = work / 'app with spaces', work / 'tools', work / 'prefix'
for p in (root, fake, prefix / 'bin', prefix / 'lib', work / 'opam'):
    p.mkdir(parents=True)
(prefix / 'bin' / 'compiler').write_text('compiler version 1\n')
(work / 'opam' / 'config').write_text('fixed switch mapping\n')
scripts = {
    'opam': '''#!/bin/sh
case "$1" in
  exec) shift; while [ "$1" != -- ]; do shift; done; shift; exec "$@" ;;
  var) case " $* " in *' prefix '*) printf '%s\\n' "$SOMA_TEST_PREFIX" ;;
           *' root '*) printf '%s\\n' "$OPAMROOT" ;; *) printf 'fake\\n' ;; esac ;;
  --version) printf '2.3.0\\n' ;;
  repo) printf 'default\\n' ;;
  monorepo) exit 0 ;;
  *) exit 2 ;;
esac
''',
    'mirage': '#!/bin/sh\nmkdir -p duniverse\n: > Makefile\n',
    'make': '''#!/bin/sh
if [ "$1" = build ]; then
  printf 'build\\n' >> "$SOMA_TEST_BUILD_CALLS"
  mkdir -p dist
  printf 'image product bytes\\n' > dist/soma.hvt
fi
''',
}
for name, contents in scripts.items():
    p = fake / name
    p.write_text(contents)
    p.chmod(0o755)
(root / 'soma.toml').write_text('[project]\nname = "fresh_app"\nversion = "0.1.0"\n')
source = root / 'main.soma'
source.write_text('Require Import Sandbox.\nmain := print "hello".\n')
calls = work / 'calls'
env = dict(os.environ)
for name in ('CFLAGS', 'CXXFLAGS', 'CPPFLAGS', 'LDFLAGS'):
    env.pop(name, None)
env.update(PATH=str(fake) + os.pathsep + env['PATH'], OPAMROOT=str(work / 'opam'),
           SOMA_TEST_PREFIX=str(prefix), SOMA_TEST_BUILD_CALLS=str(calls),
           SOMA_MIRAGE_SWITCH='fake', SOMA_MIRAGE_DIR=str(work / 'mirage'),
           SOMA_CACHE=str(work / 'shared'), XDG_CACHE_HOME=str(work / 'xdg'))
env.pop('SOMA_MIRAGE_BUILD', None)
env.pop('SOMA_MIRAGE_NO_IMAGE', None)

def run(args, success=True):
    start = time.monotonic()
    p = subprocess.run(['soma'] + args, cwd=root, env=env,
                       text=True, capture_output=True, timeout=120)
    assert (p.returncode == 0) == success, (args, p.stdout, p.stderr)
    return p, time.monotonic() - start

def build():
    return run(['build', 'main.soma'])

def fresh(success=False):
    return run(['build', '--check-fresh', 'main.soma'], success)

_, cold = build()
assert (root / 'main.hvt').is_file()
fresh()
before_calls = calls.read_text()
p, warm = build()
assert 'unchanged since its last build' not in p.stdout, p.stdout
assert calls.read_text() != before_calls, 'uncertified native validation was skipped'

# Product edits/deletion, source edits, external compiler and source dependency
# edits all require the real checking/build path again.
product = root / 'main.hvt'
old = product.stat()
product.write_bytes(b'other product bytes\n')
os.utime(product, ns=(old.st_atime_ns, old.st_mtime_ns))
fresh(False)
build()
fresh()
product.unlink()
fresh(False)
build()
fresh()
compiler = prefix / 'bin' / 'compiler'
old = compiler.stat()
compiler.write_text('compiler version 2\n')
os.utime(compiler, ns=(old.st_atime_ns, old.st_mtime_ns))
fresh(False)
build()
fresh()
library = work / 'mirage' / 'plain' / 'duniverse' / 'library.ml'
library.write_text('let version = 2\n')
fresh(False)
build()
fresh()
with (fake / 'make').open('a') as f:
    f.write('# modified tool bytes\n')
fresh(False)
build()
fresh()
override = fake / 'ocamlfind'
override.write_text('#!/bin/sh\nexit 0\n')
override.chmod(0o755)
fresh(False)
build()
fresh()

# Even an undocumented wrapper variable may affect a foreign build. Bind the
# full environment by hash, without writing its plaintext into the record.
env['PRIVATE_BUILD_SETTING'] = 'private-value-must-not-appear-in-record'
fresh(False)
build()
fresh()
for record in (root / '.soma-cache' / '.freshness').glob('*'):
    assert env['PRIVATE_BUILD_SETTING'] not in record.read_text()

# Arbitrary compiler flags may name inputs the manifest cannot enumerate.
# Continue building normally, but leave this case uncertified for skipping.
env['CFLAGS'] = '-Iunknown-extra-input'
fresh(False)
build()
fresh(False)
del env['CFLAGS']
build()
fresh()

# A failed check clears success metadata. A subsequent check command must not
# manufacture a successful product build record.
source.write_text('Require Import Sandbox.\nmain : nat := true.\n')
run(['build', 'main.soma'], False)
source.write_text('Require Import Sandbox.\nmain := print "hello".\n')
fresh(False)
run(['check', 'main.soma'])
fresh(False)
build()
fresh()

# Missing provenance remains stale even with the product bytes still present.
receipts = work / 'xdg' / 'soma-receipts'
assert receipts.is_dir()
for receipt in receipts.iterdir():
    receipt.unlink()
fresh(False)
print('uncertified image toolchains always rerun native validation: ok')
print('timings first=%.3fs repeat-validation=%.3fs' % (cold, warm))
PY
