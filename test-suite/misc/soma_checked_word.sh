#!/usr/bin/env bash
# Checked native words: exact trusted laws, actual extraction and counterexamples.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
export CHECKED_WORD_SOURCE="$root/theories/Soma/CheckedWord.v"
export CHECKED_WORD_ASSUMPTIONS="$root/test-suite/misc/soma_checked_word.assumptions.json"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
python3 - <<'PY'
from pathlib import Path
import json, os, re, subprocess

source = Path(os.environ['CHECKED_WORD_SOURCE']).read_text()
expected = json.loads(Path(os.environ['CHECKED_WORD_ASSUMPTIONS']).read_text())
names = re.findall(r'^Theorem (\w+)', source, re.M)
assert set(names) == set(expected) and len(names) == 25
for i, name in enumerate(names):
    file = Path(f'assumptions_{i}.v')
    file.write_text(f'Require Import Soma.CheckedWord.\nPrint Assumptions CheckedWord.{name}.\n')
    result = subprocess.run(['rocq', 'c', '-q', '-no-soma-prelude', str(file)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert result.returncode == 0, result.stdout
    actual = set(re.findall(r'^([A-Za-z_][\w.\x27]*)\s*:', result.stdout, re.M)) - {'Axioms'}
    assert actual == set(expected[name]), (name, actual, expected[name], result.stdout)
print('PASS: all 25 machine-word contracts match exact per-theorem primitive/law inventories', flush=True)

laws = ['Corelib.Numbers.Cyclic.Int63.' + name for name in expected['of_Z_spec']
        if name.startswith('Uint63Axioms.') or name == 'PrimInt63.int']
Path('main.soma').write_text('''From Soma Require CheckedWord NativeWord CheckedArithmetic.
From Corelib Require Import PrimInt63.
From Stdlib Require Import ZArith.
Definition convert := CheckedWord.of_Z.
Definition decode := NativeWord.signed.
Definition arithmetic left right := (CheckedWord.add left right,(CheckedWord.sub left right,CheckedWord.mul left right)).
Definition pointers position count stride := (CheckedWord.advance position count,CheckedWord.scaled_advance position count stride).
Definition main := (convert,decode,arithmetic,pointers).
Verification Properties "conversion_matches_range" Invariants "advance_respects_binary_span" Trust "''' + '; '.join(laws) + '''".
''')
Path('main.exp').write_text('''Theorem conversion_matches_range : forall value result,
 convert value = Some result <-> NativeWord.signed result = value /\\ CheckedArithmetic.fits value.
Proof. apply CheckedWord.of_Z_spec. Qed.
Theorem advance_respects_binary_span : forall position count result,
 CheckedWord.advance position count = Some result ->
 (0 <= NativeWord.signed position <= NativeWord.signed result /\\
 NativeWord.signed result <= CheckedArithmetic.maximum /\\
 NativeWord.signed result - NativeWord.signed position = count)%Z.
Proof. apply CheckedWord.advance_bounds. Qed.
''')
PY
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
python3 - <<'PY'
from pathlib import Path
import json, os, subprocess, tomllib
expected = json.loads(Path(os.environ['CHECKED_WORD_ASSUMPTIONS']).read_text())
laws = {'Corelib.Numbers.Cyclic.Int63.' + name for name in expected['of_Z_spec']
        if name.startswith('Uint63Axioms.') or name == 'PrimInt63.int'}
receipt = tomllib.loads(Path('native/verification.toml').read_text())
assert set(receipt['used-assumptions']) == laws, receipt
assert {r['name'] for r in receipt['invariants']} == {'advance_respects_binary_span'}
assert set(receipt['invariants'][0]['assumptions']) == laws
source = Path('main.soma')
original = source.read_text()
law = 'Corelib.Numbers.Cyclic.Int63.Uint63Axioms.of_to_Z'
assert original.count(law) == 1
source.write_text(original.replace(law, '').replace('; ;', ';'))
result = subprocess.run(['soma', 'extract', 'main.soma', '-no-soma-prelude', '-o', 'rejected'],
    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert result.returncode != 0 and 'of_to_Z' in result.stdout, result.stdout
source.write_text(original)
print('PASS: native verification reports the existing primitive laws and rejects an omitted law', flush=True)
PY
cp native/{soma_nat.ml,uint63.ml,soma_word64.ml,float64.ml,prog.ml,prog.mli} .
cat >check.ml <<'ML'
let checked=ref 0
let minimum=Int64.neg(Int64.shift_left 1L 62) and maximum=Int64.pred(Int64.shift_left 1L 62)
let rec positive bits=if bits=1L then Prog.XH else
 let rest=positive(Int64.shift_right_logical bits 1)in
 if Int64.logand bits 1L=0L then Prog.XO rest else Prog.XI rest
let source number=if number=0L then Prog.Z0 else if number>0L then Prog.Zpos(positive number)
 else Prog.Zneg(positive(Int64.neg number))
let rec bits=function Prog.XH->1L|Prog.XO rest->Int64.shift_left(bits rest)1
 |Prog.XI rest->Int64.logor(Int64.shift_left(bits rest)1)1L
let integer=function Prog.Z0->0L|Prog.Zpos value->bits value|Prog.Zneg value->Int64.neg(bits value)
let fits value=minimum<=value&&value<=maximum
let expected value=if fits value then Some(Int64.to_int value)else None
let equal label actual expected=incr checked;if actual<>expected then failwith label
let product left right=
 if left=0L||right=0L then Some 0 else
 let negative=(left<0L)<>(right<0L)in
 let limit=if negative then Int64.neg minimum else maximum in
 if Int64.abs left>Int64.div limit(Int64.abs right)then None
 else Some(Int64.to_int(Int64.mul left right))
let check_number value=equal "checked conversion"(Prog.convert(source value))(expected value)
let check_pair left right=
 let a=Int64.of_int left and b=Int64.of_int right in
 equal "signed input decode"(integer(Prog.decode left))a;
 let addition,(subtraction,multiplication)=Prog.arithmetic left right in
 equal "checked addition" addition(expected(Int64.add a b));
 equal "checked subtraction" subtraction(expected(Int64.sub a b));
 equal "checked multiplication" multiplication(product a b);
 Option.iter(fun value->equal "native addition refinement" value(left+right))addition;
 Option.iter(fun value->equal "native subtraction refinement" value(left-right))subtraction;
 Option.iter(fun value->equal "native multiplication refinement" value(left*right))multiplication
let check_pointer position count stride=
 let p=Int64.of_int position in
 let expected_count n=if p>=0L&&n>=0L&&n<=Int64.sub maximum p then Some(Int64.to_int(Int64.add p n))else None in
 let expected_scale=if p<0L||count<0L||stride<0L then None
  else if count=0L||stride=0L then Some position
  else if count>Int64.div(Int64.sub maximum p)stride then None
  else expected_count(Int64.mul count stride)in
 let advance,scaled=Prog.pointers position(source count)(source stride)in
 equal "checked endpoint" advance(expected_count count);
 equal "checked scaled endpoint" scaled expected_scale
let rec power n=if n=0 then Prog.XH else Prog.XO(power(n-1))
let ()=
 let values=[min_int;min_int+1;-4097;-4096;-1;0;1;2;4095;4096;4097;max_int-4096;max_int-1;max_int]in
 List.iter(fun left->check_number(Int64.of_int left);List.iter(check_pair left)values)values;
 List.iter check_number [Int64.min_int;Int64.max_int;Int64.pred minimum;Int64.succ maximum];
 List.iter(fun p->List.iter(fun n->List.iter(check_pointer p n)
  [-1L;0L;1L;2L;8L;4096L;maximum;Int64.max_int])[-1L;0L;1L;4096L;maximum;Int64.max_int])values;
 let random=Random.State.make[|63;4096;20261128|]in
 let word()=let value=(Random.State.bits random lsl 32)lor(Random.State.bits random lsl 2)lor(Random.State.bits random land 3)in
  if Random.State.bool random then value else -value in
 for i=0 to 9999 do
  let left=word()and right=word()in check_pair left right;
  let position=if i mod 2=0 then max_int-(Random.State.int random 1000000)else Random.State.int random 1000000 in
  check_pointer position(Int64.of_int(Random.State.int random 10000-1))(Int64.of_int(Random.State.int random 4098-1))
 done;
 List.iter(fun n->let positive=Prog.Zpos(power n)and negative=Prog.Zneg(power n)in
  equal "large positive rejected"(Prog.convert positive)None;
  equal "large negative rejected"(Prog.convert negative)None;
  let advance,scaled=Prog.pointers max_int positive positive in
  equal "large count rejected" advance None;equal "large scaled count rejected" scaled None;
  let _,zero=Prog.pointers max_int Prog.Z0 positive in
  equal "zero count with huge stride retains endpoint" zero(Some max_int);
  let _,invalid=Prog.pointers max_int Prog.Z0 negative in equal "negative stride still rejected" invalid None
 )[63;80;128;1024];
 Printf.printf "PASS: %d checked word conversions/arithmetic/native refinements/endpoints against independent Int64 guards\n%!"!checked
ML
for backend in ocamlopt ocamlc; do
 "$backend" -w -a soma_nat.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml -o "check-$backend" >"$backend.log" 2>&1
 "./check-$backend"
done
python3 - <<'PY'
from pathlib import Path
import os, re, subprocess
source = Path(os.environ['CHECKED_WORD_SOURCE']).read_text()
def change(before, after):
    assert source.count(before) == 1, before
    return source.replace(before, after)
cases = [
 ('baseline', source, None),
 ('zero_encoding', change('Definition encode := Uint63Axioms.of_Z.',
    'Definition encode (_ : Z) := 0%uint63.'), 'decode_encode'),
 ('wrapped_addition', change('Definition add left right := of_Z (NativeWord.signed left + NativeWord.signed right).',
    'Definition add left right := of_Z (NativeWord.signed (PrimInt63.add left right)).'), 'add_spec'),
 ('wrong_endpoint', change('Some (encode (CheckedArithmetic.ending range))',
    'Some (encode (CheckedArithmetic.beginning range))'), 'advance_spec'),
 ('missing_stride_guard', change('if Z.leb 0 count && Z.leb 0 stride then advance position (count * stride) else None.',
    'if Z.leb 0 count then advance position (count * stride) else None.'), 'scaled_advance_spec'),
]
for name, text, theorem in cases:
    file = Path('mutation_' + name + '.v')
    file.write_text(text)
    result = subprocess.run(['rocq', 'c', '-q', '-no-soma-prelude', str(file)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if theorem is None:
        assert result.returncode == 0, result.stdout
        continue
    assert result.returncode != 0, name + ': changed implementation passed'
    begin = text.index('Theorem ' + theorem)
    first = text[:begin].count('\n') + 1
    last = text[:text.index('Qed.', begin)].count('\n') + 1
    assert any(first <= int(line) <= last for line in re.findall(r'line (\d+),', result.stdout)), result.stdout
    print('PASS: ' + theorem + ' rejects ' + name, flush=True)
PY
