#!/usr/bin/env bash
# Real arithmetic/boundary/coverage changes must be rejected by their proofs.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export CHECKED_MEMORY_SOURCE="$root/theories/Soma"
cd "$work"
python3 - <<'PY'
from pathlib import Path
import os, re, subprocess

root = Path(os.environ['CHECKED_MEMORY_SOURCE'])
arithmetic = (root / 'CheckedArithmetic.v').read_text()
geometry = (root / 'PageGeometry.v').read_text()

def changed(source, old, new):
    assert source.count(old) == 1, old
    return source.replace(old, new)

cases = [
    ('arithmetic_baseline', arithmetic, None),
    ('geometry_baseline', geometry, None),
    ('wrong_addition', changed(arithmetic, 'Definition add left right := checked (left + right).',
        'Definition add left right := checked (left - right).'), 'add_spec'),
    ('nonforward_page', changed(geometry, 'Definition page_end address := page_base address + page_size.',
        'Definition page_end address := page_base address.'), 'page_interval'),
    ('nonforward_boundary', changed(geometry, 'if Z.ltb address candidate && Z.ltb candidate before then candidate else before.',
        'if Z.ltb address candidate && Z.ltb candidate before then address else before.'), 'selected_boundary_progress'),
    ('oversized_piece', changed(geometry, 'Definition piece_end window stop cursor := Z.min stop (run_end window cursor).',
        'Definition piece_end window stop cursor := Z.max stop (run_end window cursor).'), 'piece_progress'),
    ('empty_partition', changed(geometry, 'partition_walk window (Z.to_nat (CheckedArithmetic.length range))',
        'partition_walk window 0%nat'), 'partition_covers'),
]
for name, source, expected in cases:
    file = Path(name + '.v')
    file.write_text(source)
    result = subprocess.run(['rocq', 'c', '-q', '-no-soma-prelude', str(file)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if expected is None:
        assert result.returncode == 0, result.stdout
        continue
    assert result.returncode != 0, name + ': corrupted implementation passed'
    error = re.search(r'line (\d+),', result.stdout)
    assert error, result.stdout
    prefix = '\n'.join(source.splitlines()[:int(error[1])])
    names = re.findall(r'^(?:Theorem|Lemma) (\w+)', prefix, re.M)
    assert names and names[-1] == expected, f'{name}: expected {expected}:\n{result.stdout}'
    print(f'PASS {name}: rejected by {expected}')
print('PASS: checked arithmetic/geometry baselines and five actual corruption rejections')
PY
