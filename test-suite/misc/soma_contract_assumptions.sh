#!/usr/bin/env bash
# Keep the new contract proofs honest about their trust base. Ordinary
# arithmetic/protocol proofs must be closed. Crypto may use only the listed
# existing Uint63 primitives/specifications; cast laws only gradual primitives.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cd "$WORK"
python3 - <<'PY'
from pathlib import Path
import re, subprocess
checks = {
 'native': ('Soma.NativeSpec', ['Native.signed_exact', 'Native.add_refines', 'Native.mul_refines',
    'Native.sub_refines', 'Native.add_guard', 'Native.mul_guard', 'Native.decimal18_fits64',
    'Native.add_overflow_is_not_nat_add', 'Native.decimal18_product_needs_another_bound']),
 'native_semantics': ('Soma.NativeSemantics', ['steps_trans', 'steps_bind', 'steps_protect',
    'invocation_raise_reaches_handler', 'loop_finishes', 'loop_continues', 'loop_has_terminating_execution',
    'spinning_loop_diverges',
    'reference_roundtrip', 'callback_write_then_raise', 'writes_read_back', 'writes_keep_identities',
    'writes_preserve_other_reads', 'writes_preserve_well_formed', 'allocation_preserves_well_formed',
    'empty_world_well_formed', 'step_preserves_well_formed', 'steps_preserve_well_formed']),
 'wire': ('Soma.Wire', ['prefix_decodes', 'split_at_walk_append_length', 'frame_roundtrip', 'frame_roundtrip_default']),
 'host': ('Soma.HostSpec', ['SocketWrites.advance_preserves_bytes',
    'SocketWrites.advance_past_end', 'SocketWrites.writes_preserve_bytes']),
 'storage': ('Soma.StorageSpec', ['SnapshotRecovery.every_commit_prefix_recovers_old_or_new',
    'SnapshotRecovery.acknowledged_commit_recovers_new', 'SnapshotRecovery.committed_write_readback',
    'SnapshotRecovery.committed_write_preserves_other']),
 'crypto': ('Soma.CryptoSpec', ['LimbSpec.split31', 'LimbSpec.add_carry1_correct',
    'LimbSpec.add_carry_correct', 'LimbSpec.mul_limb_correct', 'LimbSpec.mul_big_correct',
    'LimbSpec.trim_preserves_value']),
 'cast': ('Soma.CastSpec', ['nat_roundtrip', 'bool_roundtrip', 'list_nat_roundtrip',
    'string_roundtrip', 'option_nat_roundtrip', 'pair_roundtrip', 'function_roundtrip',
    'nat_to_bool_fails', 'bool_to_nat_fails', 'unknown_stays_unknown', 'error_stays_error',
    'tagged_nat_even', 'tagged_nat_odd', 'tagged_bool_even', 'tagged_bool_odd'])
}
crypto = {'PrimInt63.' + name for name in
    ['int', 'add', 'sub', 'mul', 'land', 'lor', 'lsl', 'lsr', 'ltb', 'leb', 'eqb']}
crypto |= {'Uint63Axioms.' + name for name in
    ['add_spec', 'sub_spec', 'mul_spec', 'land_spec', 'lor_spec', 'lsl_spec', 'lsr_spec',
     'ltb_spec', 'leb_spec', 'eqb_correct', 'eqb_refl', 'of_to_Z']}
cast = {'Gradual.unknown', 'Gradual.err', 'Gradual.cast'}
for group, (module, theorems) in checks.items():
    allowed = (crypto if group == 'crypto' else cast if group == 'cast'
               else {'PrimInt63.int'} if group == 'native_semantics' else set())
    for index, theorem in enumerate(theorems):
        source = Path(f'{group}_{index}.v')
        source.write_text(f'Require Import {module}.\nPrint Assumptions {theorem}.\n')
        result = subprocess.run(['rocq', 'c', '-q', '-no-soma-prelude', str(source)],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert result.returncode == 0, result.stdout
        names = set(re.findall(r'^([A-Za-z_][\w.\x27]*)\s*:', result.stdout, re.M)) - {'Axioms'}
        if 'Axioms:' in result.stdout:
            assert names, result.stdout
        else:
            assert 'Closed under the global context' in result.stdout, result.stdout
        assert names <= allowed, f'{theorem}: unexpected assumptions {names - allowed}\n{result.stdout}'
    print(f'PASS {group}: {len(theorems)} contract theorem assumption sets')
PY
