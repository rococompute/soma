#!/usr/bin/env bash
# Default gradual functor extraction preserves application identity in both
# file output and interactive/recursive inspection commands.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_AUDIT_SOURCE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
python3 - <<'PY'
import os, pathlib, subprocess, tempfile
fixture = pathlib.Path(os.environ['SOMA_AUDIT_SOURCE_ROOT']) / \
    'test-suite/misc/soma_audit_shared_gradual/functor_identity.v'
body = fixture.read_text()
body = body[:body.rindex('Extraction "Functor"')]
env = dict(os.environ)
env.pop('SOMA_EXPERIMENTAL_SHARED_EXTRACTION', None)
commands = ['Extraction "output" roundtrip wrong_inside.',
            'Recursive Extraction roundtrip wrong_inside.',
            'Extraction roundtrip.']
with tempfile.TemporaryDirectory(prefix='soma-functor-guard-') as tmp:
    root = pathlib.Path(tmp)
    for index, command in enumerate(commands):
        source = root / ('Guard%d.v' % index)
        source.write_text(body + command + '\n')
        result = subprocess.run(['rocq', 'c', '-q', source.name], cwd=root,
                                env=env, text=True, capture_output=True, timeout=60)
        assert result.returncode == 0, (command, result.stdout, result.stderr)
        if index == 0:
            (root / 'check.ml').write_text(
                'let () = assert (Output.Gradual_rt.is_error (Output.wrong_inside ()));\n'
                ' match Output.Gradual_rt.force (Output.roundtrip ()) with\n'
                ' | Output.N.B1 _ -> () | _ -> failwith "wrong constructor"\n')
            for args in [['ocamlc', '-w', '-a', 'output.mli', 'output.ml', 'check.ml', '-o', 'check.exe'],
                         ['./check.exe']]:
                compiled = subprocess.run(args, cwd=root, env=env, text=True, capture_output=True, timeout=60)
                assert compiled.returncode == 0, (args, compiled.stdout, compiled.stderr)
print('default gradual functor file and inspection extraction preserve application identity: ok')
PY
