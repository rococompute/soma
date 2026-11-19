#!/usr/bin/env bash
# A top-level Include is a semantic alias even when the monolithic type
# printer deliberately duplicates its declaration with ind_equiv=NoEquiv.
set -euo pipefail
export PATH="$BIN:$PATH"
python3 - <<'PY'
import os, pathlib, subprocess, tempfile
with tempfile.TemporaryDirectory(prefix='soma-brand-file-alias-') as tmp:
    root = pathlib.Path(tmp)
    (root / 'Origin.v').write_text('From Corelib.Gradual Require Import Gradual.\n'
        'Inductive t : Type := T0 : t | T1 : nat -> t.\n'
        'Definition inject (n : nat) : Any := cast t Any (T1 n).\n')
    (root / 'Alias.v').write_text('Require Import Origin.\n'
        'From Corelib.Gradual Require Import Gradual.\nInclude Origin.\n'
        'Definition project (x : Any) : t := cast Any t x.\n')
    (root / 'Consumer.v').write_text('Require Import Origin Alias.\n'
        'From Corelib.Gradual Require Import Gradual.\n'
        'Definition roundtrip (_ : unit) : Alias.t := Alias.project (Origin.inject 2).\n'
        'Definition observe (_ : unit) : nat := match roundtrip tt with Alias.T0 => 0 | Alias.T1 n => n end.\n'
        'Goal roundtrip tt = Alias.T1 2. Proof. reflexivity. Qed.\n'
        'Goal observe tt = 2. Proof. reflexivity. Qed.\n'
        'From Corelib Require Extraction.\nExtract Inductive unit => "unit" [ "()" ].\n'
        'Extraction "AliasMono" roundtrip observe.\n')
    (root / 'check.ml').write_text('let rec nat = function AliasMono.O -> 0 | AliasMono.S n -> 1 + nat n\n'
        'let () = assert (nat (AliasMono.Gradual_rt.force (AliasMono.observe ())) = 2); '
        'print_endline "file Include alias matches kernel behavior: ok"\n')
    for enabled in [False, True]:
        env = dict(os.environ)
        env.pop('SOMA_EXPERIMENTAL_SHARED_EXTRACTION', None)
        if enabled:
            env['SOMA_EXPERIMENTAL_SHARED_EXTRACTION'] = '1'
        commands = [['rocq', 'c', '-q', f] for f in ['Origin.v', 'Alias.v', 'Consumer.v']]
        commands += [['ocamlc', '-w', '-a', 'AliasMono.mli', 'AliasMono.ml', 'check.ml', '-o', 'check.exe'],
                     ['./check.exe']]
        for args in commands:
            result = subprocess.run(args, cwd=root, env=env, text=True, capture_output=True, timeout=60)
            assert result.returncode == 0, (enabled, args, result.returncode, result.stdout, result.stderr)
print('top-level canonical alias brands preserved in default and experimental modes: ok')
PY
