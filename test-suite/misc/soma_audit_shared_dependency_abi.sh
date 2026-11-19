#!/usr/bin/env bash
# Nonrecursive Library extraction must not silently link an old, unguarded
# runtime-free helper into a gradual program. Re-extraction is the recovery.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_EXPERIMENTAL_SHARED_EXTRACTION=1
python3 - <<'PY'
import os, pathlib, subprocess, tempfile
with tempfile.TemporaryDirectory(prefix='soma-shared-dependency-') as tmp:
    root = pathlib.Path(tmp).resolve()
    out = root / 'out'
    env = dict(os.environ)
    def run(args, cwd=root):
        result = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True, timeout=60)
        assert result.returncode == 0, (args, result.returncode, result.stdout, result.stderr)
        return result
    (root / 'PureProducer.v').write_text('Module Datatypes. Definition witness := 0. End Datatypes.\n'
        'Definition generic_head {A : Type} (fallback : A) (xs : list A) : A :=\n'
        ' match xs with nil => fallback | cons x _ => x end.\n')
    (root / 'PureRequest.v').write_text('Require PureProducer.\nFrom Corelib Require Extraction.\n'
        'Extraction NoInline PureProducer.Datatypes.witness.\n'
        'Set Extraction Output Directory "%s".\n'
        'Separate Extraction PureProducer.generic_head PureProducer.Datatypes.witness.\n' % out)
    run(['rocq', 'c', '-q', '-no-soma-prelude', 'PureProducer.v'])
    run(['rocq', 'c', '-q', '-no-soma-prelude', 'PureRequest.v'])
    previous = (out / 'PureProducer.ml').read_bytes()
    assert b'Gradual_rt' not in previous and (b'match' in previous or b'function' in previous), previous
    (root / 'Consumer.v').write_text('Require PureProducer.\n'
        'From Corelib.Gradual Require Import Gradual.\n'
        'Definition unknown_list (_ : unit) : list nat := unk.\n'
        'Definition trigger (_ : unit) : nat := PureProducer.generic_head 0 (unknown_list tt).\n'
        'Definition witness := PureProducer.Datatypes.witness.\n'
        'Goal trigger tt = unk. Proof. reflexivity. Qed.\n')
    run(['rocq', 'c', '-q', 'Consumer.v'])
    prefix = ('Require Consumer.\nFrom Corelib Require Extraction.\n'
              'Extract Inductive unit => "unit" [ "()" ].\n'
              'Extraction NoInline PureProducer.generic_head PureProducer.Datatypes.witness.\n'
              'Set Extraction Output Directory "%s".\n' % out)
    (root / 'Request.v').write_text(prefix +
        'Separate Extraction Consumer.unknown_list.\nExtraction Library Consumer.\n')
    run(['rocq', 'c', '-q', 'Request.v'])
    assert (out / 'PureProducer.ml').read_bytes() == previous, 'fixture rewrote stale helper'
    def compile_all(expect_rejection):
        for pattern in ['*.cmi', '*.cmo']:
            for path in out.glob(pattern):
                path.unlink()
        sources = sorted(path.name for path in out.glob('*.ml'))
        order = run(['ocamldep', '-sort'] + sources, out).stdout.split()
        for source in order:
            interface = pathlib.Path(source).with_suffix('.mli')
            if (out / interface).exists():
                run(['ocamlc', '-w', '-a', '-c', str(interface)], out)
            result = subprocess.run(['ocamlc', '-w', '-a', '-c', source], cwd=out,
                                    env=env, text=True, capture_output=True, timeout=60)
            if result.returncode:
                assert expect_rejection, (source, result.stderr)
                assert 'requires_reextraction' in result.stderr, result.stderr
                return None
        assert not expect_rejection, 'stale pure dependency was silently accepted'
        return order
    compile_all(True)
    (root / 'Recovery.v').write_text(prefix + 'Recursive Extraction Library Consumer.\n')
    run(['rocq', 'c', '-q', 'Recovery.v'])
    guarded = (out / 'PureProducer.ml').read_text()
    assert 'Gradual_rt.check' in guarded or 'Gradual_rt.propagate' in guarded, guarded
    order = compile_all(False)
    (out / 'main.ml').write_text('let () = try\n'
        ' ignore (Consumer.Gradual_rt.force (Consumer.trigger ())); failwith "unguarded stale helper"\n'
        ' with Consumer.Gradual_rt.Unknown_term _ -> print_endline "guarded dependency after recursive recovery: ok"\n')
    run(['ocamlc', '-w', '-a'] + [str(pathlib.Path(s).with_suffix('.cmo')) for s in order] +
        ['main.ml', '-o', 'main.exe'], out)
    run(['./main.exe'], out)
print('stale pure dependency ABI rejected; recursive re-extraction restores guarded execution: ok')
PY
