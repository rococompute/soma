#!/usr/bin/env bash
# Until application-aware brand code passes full execution acceptance, every
# default gradual functor extraction mode must fail before unsafe code output.
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
        assert result.returncode != 0, (command, result.stdout, result.stderr)
        assert 'application-aware runtime type identities' in ' '.join(result.stderr.split()), result.stderr
        assert not list(root.glob('*.ml*')), list(root.iterdir())
print('default unsafe gradual functor extraction is explicitly refused in all modes: ok')
PY
