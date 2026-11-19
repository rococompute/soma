#!/usr/bin/env python3
"""Actual compiler compile-count regression for module reuse across source keys."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument('--soma', required=True)
parser.add_argument('--evidence', help='preserve controlled fixture outputs, cache files and producer receipts')
parser.add_argument('--observe', action='store_true', help='record baseline without enforcing improved counts')
args = parser.parse_args()
compiler = str(Path(args.soma).resolve())
records = []

with tempfile.TemporaryDirectory(prefix='soma-module-donor-') as tmp:
    outer = Path(tmp).resolve()
    env = dict(os.environ, SOMA_CACHE=str(outer/'store'),
               XDG_CACHE_HOME=str(outer/'xdg'), SOMA_MIRAGE_BUILD='0',
               SOMA_OCAML_BUILD='0')

    def checkout(name, one=1, independent=40, main_comment=''):
        root = outer/name
        root.mkdir()
        (root/'soma.toml').write_text('[project]\nname="donors"\nversion="0.1.0"\n')
        (root/'a.soma').write_text(f'one : nat := {one}.\n')
        (root/'b.soma').write_text('Import a.\nanswer : nat := one + 1.\n')
        (root/'independent.soma').write_text(f'standalone : nat := {independent}.\n')
        (root/'main.soma').write_text(main_comment+'Import b.\nImport independent.\nanswer + standalone.\n')
        return root

    def build(root, expected, count, extra=()):
        run = subprocess.run([compiler, 'build', '-v', *extra, 'main.soma'], cwd=root,
                             env=env, text=True, capture_output=True, timeout=90)
        assert run.returncode == 0, (root.name, run.stdout, run.stderr)
        assert re.search(r'=\s*'+str(expected)+r'\b', run.stdout), (root.name, run.stdout)
        compiles = re.findall(r'^Compiling ([^\n]+)', run.stderr, re.MULTILINE)
        rec = {'case':root.name, 'result':expected, 'actual_compiles':len(compiles),
               'expected_compiles':count, 'modules':compiles}
        rec['stdout'] = run.stdout
        rec['stderr'] = run.stderr
        if args.evidence:
            artifact = Path(args.evidence).resolve()/root.name
            artifact.mkdir(parents=True)
            (artifact/'stdout.txt').write_text(run.stdout)
            (artifact/'stderr.txt').write_text(run.stderr)
            shutil.copytree(root/'.soma-cache', artifact/'cache', symlinks=True)
            receipts = outer/'xdg/soma-receipts'
            shutil.copytree(receipts, artifact/'receipts', symlinks=True)
            rec['cache_sha256'] = {str(f.relative_to(artifact/'cache')):hashlib.sha256(f.read_bytes()).hexdigest()
                                   for f in (artifact/'cache').rglob('*') if f.is_file() and not f.is_symlink()}
            rec['receipts'] = sorted(f.name for f in receipts.iterdir())
        records.append(rec)
        if not args.observe:
            assert len(compiles)==count, rec

    build(checkout('seed'), 42, 3)
    # Whole-project identity changes; a and b remain identical.
    build(checkout('unrelated-module-change', independent=41), 43, 1)
    # Entry-point edits should not recheck any unchanged imported module.
    build(checkout('entry-only-change', main_comment='(* new entry comment *)\n'), 42, 0)
    # Existing b source matches, but its selected a interface changed.
    build(checkout('dependency-interface-change', one=2), 43, 2)
    # User escape hatch must disable both project and per-module donors.
    build(checkout('disabled-cache', main_comment='(* cache disabled *)\n'), 42, 3,
          ('--no-module-cache',))

    # The two real .vo files have identical source hashes but distinct kernel
    # library names. Moving an entirely trusted A pair/descriptor into B's
    # candidate directory must not relabel it as B.
    def twins(name, comment=''):
        root = outer/name
        root.mkdir()
        (root/'soma.toml').write_text('[project]\nname="donors"\nversion="0.1.0"\n')
        for unit in ['a', 'b']:
            (root/(unit+'.soma')).write_text('value : nat := 7.\n')
        (root/'main.soma').write_text(comment+'Import a.\nImport b.\na.value + b.value.\n')
        return root
    seed = twins('wrong-library-seed')
    build(seed, 14, 2)
    if not args.observe:
        hashes = {u:hashlib.sha256((seed/'.soma-cache'/(u+'.vo')).read_bytes()).hexdigest()
                  for u in ['a', 'b']}
        candidates = {}
        for descriptor in (outer/'store/modules-v1').rglob('descriptor'):
            text = descriptor.read_text()
            for unit in ['a', 'b']:
                if ('unit "'+unit+'"\n') in text and ('object '+hashes[unit]+'\n') in text:
                    candidates[unit] = descriptor.parent
        assert set(candidates) == {'a', 'b'}, candidates
        for artifact in ['object.vo', 'object.stamp', 'descriptor']:
            shutil.copyfile(candidates['a']/artifact, candidates['b']/artifact)
    # In baseline observation mode there are no donor descriptors yet; this
    # still records baseline's two compilations. Fixed mode poisons a real
    # trusted candidate and requires just B to be safely recompiled.
    build(twins('wrong-library-candidate', '(* distinct entry *)\n'), 14, 1)
    if args.evidence:
        shutil.copytree(outer/'store', Path(args.evidence).resolve()/'shared-store', symlinks=True)

print(json.dumps({'compiler':compiler, 'mode':'baseline-observation' if args.observe else 'assert-fixed',
                  'checks':records}, indent=2))
