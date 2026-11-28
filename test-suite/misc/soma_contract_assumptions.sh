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
 'native_semantics': ('Soma.NativeSemantics', [
    'steps_trans',
    'steps_bind',
    'steps_protect',
    'invocation_raise_reaches_handler',
    'loop_finishes',
    'loop_continues',
    'loop_has_terminating_execution',
    'spinning_loop_diverges',
    'reference_roundtrip',
    'callback_write_then_raise',
    'empty_vectors_share_handle',
    'vector_replace_roundtrip',
    'buffer_append_roundtrip',
    'distinct_allocated_faults',
    'writes_read_back',
    'writes_keep_identities',
    'writes_preserve_other_reads',
    'writes_preserve_well_formed',
    'allocation_preserves_well_formed',
    'empty_world_well_formed',
    'native_bounds_preserve_world',
    'bytecode_bounds_allocate_fault',
    'bounds_preserve_well_formed',
    'same_identities_preserve_well_formed',
    'array_updates_read_back',
    'text_updates_read_back',
    'array_updates_keep_identities',
    'text_updates_keep_identities',
    'array_updates_preserve_well_formed',
    'text_updates_preserve_well_formed',
    'array_updates_preserve_shapes',
    'replace_nth_length',
    'replace_nth_readback',
    'replace_nth_preserves_other',
    'array_updates_preserve_other_reads',
    'text_updates_preserve_other_reads',
    'writes_preserve_array_contents',
    'writes_preserve_text_contents',
    'array_updates_preserve_other_arrays',
    'text_updates_preserve_other_text',
    'writes_preserve_storage_bounds',
    'array_updates_preserve_storage_bounds',
    'text_updates_preserve_storage_bounds',
    'allocate_preserves_storage_bounds',
    'bounds_preserve_storage_bounds',
    'step_preserves_well_formed',
    'steps_preserve_well_formed',
    'step_preserves_storage_bounds',
    'steps_preserve_storage_bounds',
    'step_preserves_backend',
    'steps_preserve_backend',
]),
 'native_word': ('Soma.NativeWord', [
    'bounded_index_sound',
    'bounded_index_complete',
    'bounded_index_negative',
    'bounded_index_past_end',
    'bounded_index_empty',
    'bounded_slice_sound',
    'bounded_slice_complete',
    'bounded_slice_negative_offset',
    'bounded_slice_negative_count',
    'bounded_slice_past_end',
]),
 'native_total': ('Soma.NativeTotal', [
    'reachable_preserves_invariant',
    'rank_gives_accessibility',
    'ranked_total_correctness',
    'safe_after_step',
    'total_preserved_by_step',
    'total_preserved_by_execution',
    'total_has_successful_or_exceptional_execution',
    'accessible_excludes_divergence',
    'total_excludes_divergence',
    'total_maximal_execution_satisfies',
    'stuck_without_postcondition_is_not_total',
    'return_is_total',
    'throw_is_total',
    'outcome_injective',
    'total_outcome_requires_postcondition',
    'successors_give_total',
    'spinning_loop_is_not_total',
    'ranked_execution_length',
    'total_requires_every_foreign_return',
    'total_requires_every_foreign_exception',
    'allowed_false_return_rejects_true_only_spec',
    'total_entry_runs_satisfy',
    'total_entry_has_execution',
    'unsupported_table_is_not_total',
]),
 'native_control': ('Soma.NativeControl', [
    'step_control_successor',
    'total_bind',
    'total_bind_return',
    'total_invoke',
    'total_loop_unroll',
    'total_loop_step',
    'total_loop_continue',
    'total_loop_finish',
]),
 'native_text': ('Soma.NativeText', [
    'text_index_fits_carrier',
    'text_get_defined',
    'text_slice_length',
    'step_string_successor',
    'string_length_total',
    'string_get_total',
    'string_get_invalid_total',
    'string_get_nat_total',
    'string_get_nat_invalid_total',
    'string_substring_total',
    'string_substring_invalid_total',
]),
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
# Bit interpretation/encoding uses existing kernel operations, not new word laws.
native_word = {'PrimInt63.' + name for name in
    ['int', 'sub', 'ltb', 'eqb', 'land', 'lor', 'lsl', 'lsr']}
for group, (module, theorems) in checks.items():
    allowed = (crypto if group == 'crypto' else cast if group == 'cast'
               else native_word if group in {'native_semantics','native_word','native_total','native_control','native_text'} else set())
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
