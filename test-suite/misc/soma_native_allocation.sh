#!/usr/bin/env bash
# Owned allocation must certify its actual handle/world, never its stored body.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
export ALLOCATION_SOURCE="$root/theories/Soma/NativeAllocation.v"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >check.v <<'COQ'
From Soma Require Import Native NativeSemantics NativeTotal NativeAllocation.
From Stdlib Require Import Strings.String.
Definition no_foreign A (_:unit->A) (_:world) (_:result A) (_:world) := False.
Definition no_named A B (_ _:string) (_:A) (_:world) (_:result B) (_:world) := False.
Definition spinning_factory (_:Native.callback unit unit) (_:unit) : Native.program unit :=
  Native.Loop (fun state => Native.Return (Native.Continue state)) tt.
Example allocating_does_not_execute_stored_body :
  total no_foreign no_named (fun final answer =>
    final = callback_world empty_world spinning_factory /\
    answer = Returned (@Native.Callback unit unit 0))
    (empty_world,Native.New_callback spinning_factory).
Proof. apply new_callback_is_total. split; reflexivity. Qed.
Example allocation_cannot_certify_false w factory :
  ~ total no_foreign no_named (fun _ _ => False) (w,@Native.New_callback unit unit factory).
Proof.
  intro Total. exact (@new_callback_requires_postcondition no_foreign no_named unit unit
    (fun _ _=>False) w factory Total).
Qed.
Example binding_returns_actual_fresh_handle :
  total no_foreign no_named (fun final answer =>
    final = callback_world empty_world spinning_factory /\
    answer = Returned (@Native.Callback unit unit 0))
    (empty_world,Native.Bind (Native.New_callback spinning_factory) Native.Return).
Proof. apply bind_new_callback_is_total, return_is_total. split; reflexivity. Qed.
COQ
rocq c -q -no-soma-prelude check.v >check.log 2>&1
echo 'PASS: owned callback allocation, exact fresh state/handle, unexecuted spinning body and rejection of false postconditions'
python3 - <<'PY'
from pathlib import Path
import os, re, subprocess
source=Path(os.environ['ALLOCATION_SOURCE']).read_text()
def change(before,after):
    assert source.count(before)==1,before
    return source.replace(before,after)
cases=[('baseline',source,None),
       ('wrong_world',change('allocate w (Callback_cell (next_id w) (factory (Native.Callback (next_id w)))).',
                             'w.'),'step_callback_successor'),
       ('wrong_continuation_handle',change('(callback_world w factory, next (Native.Callback (next_id w))) ->',
                                           '(callback_world w factory, next (Native.Callback (S (next_id w)))) ->'),
                                    'bind_new_callback_is_total')]
for name,text,theorem in cases:
    file=Path('mutation_'+name+'.v');file.write_text(text)
    result=subprocess.run(['rocq','c','-q','-no-soma-prelude',str(file)],capture_output=True,text=True)
    if theorem is None:
        assert result.returncode==0,result.stdout+result.stderr
        continue
    assert result.returncode!=0,name+': changed allocation contract passed'
    begin=text.index('Theorem '+theorem)
    first=text[:begin].count('\n')+1
    last=text[:text.index('Qed.',begin)].count('\n')+1
    assert any(first<=int(line)<=last for line in re.findall(r'line (\d+),',result.stdout+result.stderr)),result.stdout+result.stderr
    print('PASS: '+theorem+' rejects '+name,flush=True)
PY
