#!/usr/bin/env python3
"""Actual compiler compile-count regression for module reuse across source keys."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument('--soma', required=True)
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

print(json.dumps({'compiler':compiler, 'mode':'baseline-observation' if args.observe else 'assert-fixed',
                  'checks':records}, indent=2))
