#!/usr/bin/env bash
# Check that the byte-level language theorems reject decision corruption.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export IPV4_GRAMMAR_SOURCE="$root/theories/Soma/IPv4.v"
cd "$work"
python3 - <<'PY'
from pathlib import Path
import os, re, subprocess

original = Path(os.environ['IPV4_GRAMMAR_SOURCE']).read_text()

def changed_once(old, new):
    assert original.count(old) == 1, old
    return original.replace(old, new)

cases = [
    ('digit_classifier', changed_once('if Ascii.eqb character "0"%char then Some 0 else',
        'if Ascii.eqb character "0"%char then Some 1 else'), 'digit_code'),
    ('decimal_value', changed_once('roll accumulator next)\n      end',
        'roll accumulator 0)\n      end'), 'digits_span'),
    ('octal_guard', changed_once('if Ascii.eqb first "0"%char then',
        'if false then'), 'octet_token_sound'),
    ('quad_value', changed_once('@Address (((a * 256 + b) * 256 + c) * 256 + d)',
        '@Address (((a * 256 + b) * 256 + c) * 256 + c)'), 'checked_quad_geometry'),
    ('quad_delimiter', changed_once('bind (octet text cursor) (fun a cursor => bind (expect text cursor "."%char)',
        'bind (octet text cursor) (fun a cursor => bind (expect text cursor "/"%char)'), 'quad_success_grammar'),
    ('end_of_input', changed_once('None => Ready item cursor | Some character => Failed (Bad_character character cursor) end).',
        'None => Ready item cursor | Some character => Ready item cursor end).'), 'of_string_success_grammar'),
]

for name, source, expected in [('unchanged', original, None)] + cases:
    path = Path(name + '.v')
    path.write_text(source)
    result = subprocess.run(['rocq', 'c', '-q', '-no-soma-prelude', str(path)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if expected is None:
        assert result.returncode == 0, result.stdout
        continue
    assert result.returncode != 0, f'{name}: a corrupted parser passed its grammar proofs'
    error = re.search(r'line (\d+),', result.stdout)
    assert error, result.stdout
    prefix = '\n'.join(source.splitlines()[:int(error[1])])
    proofs = re.findall(r'^(?:Theorem|Lemma) (\w+)', prefix, re.M)
    assert proofs and proofs[-1] == expected, f'{name}: expected {expected}:\n{result.stdout}'
    print(f'PASS {name}: rejected by {expected}')
print('PASS: unchanged parser grammar checks; six actual decision corruptions rejected')
PY
