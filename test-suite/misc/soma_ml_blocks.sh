#!/usr/bin/env bash
# ML blocks elaborate to ordinary Soma terms, including precisely the existing
# Sandbox.bind tree. Proofs check syntax lowering, scoping and evaluation order.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
cat > "$WORK/blocks.soma" <<'SOMA'
Require Import Sandbox.
ml : nat := 9.
function : nat := 17.
and : nat := 4.
x : nat := 9.
y : nat := 8.
_ml_argument0 : nat := 5.
plain := ml { let n = 2 in n + 3 * 4 }.
parallel := ml { let x = 1 and y = x and z = y in x + y + z }.
local_function := ml { let twice (n : nat) = n + n in twice 4 }.
lam := ml { (fun n -> n + 1) 4 }.
choose := ml { function Some n -> n + _ml_argument0 | None -> 0 }.
match_list := ml { match [1;2;3] with [] -> 0 | h :: _ -> h }.
match_nested := ml { match Some (Some 3) with Some v -> (match v with Some n -> n | None -> 0) | None -> 4 }.
condition := ml { if 2 <? 3 then 6 else 7 }.
pair := ml { (2,3) }.
triple := ml { (2,3,4) }.
destructured := ml { let (a,b) = (2,3) in a+b }.
annotation : N := ml { (3 : N) + 4 }%N.
scoped_call := ml { N.add 3%N 4%N }.
negative : Z := ml { -3 + 1 }%Z.
prop_equal : Prop := ml { 1 = 1 }.
bool_equal : bool := ml { 1 =? 1 }.
escape := ml { let n = soma { let k := 4 in k + 1 } in n + 1 }.
nested := ml { let n = ml { let k = 4 in k + 1 } in n + 1 }.
legacy := let k := 2 in (fun x => match x with O => 3 | S n => n end) k.
identity_names := ml + function + and.
read_update (c : cell nat) : io nat := ml {
  let* n = read_cell c in
  write_cell c (n+1);
  ret n
}.
read_pair (c : cell (nat * nat)) : io nat := ml {
  let* (a,b) = read_cell c in
  ret (a+b)
}.
SOMA
cat > "$WORK/blocks.exp" <<'SOMA'
Example arithmetic : plain = 14. Proof. reflexivity. Qed.
Example simultaneous : parallel = 18. Proof. reflexivity. Qed.
Example local_fun : local_function = 8. Proof. reflexivity. Qed.
Example lambda : lam = 5. Proof. reflexivity. Qed.
Example function_hygiene : choose (Some 3) = 8. Proof. reflexivity. Qed.
Example function_none : choose None = 0. Proof. reflexivity. Qed.
Example matched : match_list = 1. Proof. reflexivity. Qed.
Example nested_match : match_nested = 3. Proof. reflexivity. Qed.
Example conditional : condition = 6. Proof. reflexivity. Qed.
Example tuple_pair : pair = (2,3). Proof. reflexivity. Qed.
Example tuple_triple : triple = (2,3,4). Proof. reflexivity. Qed.
Example tuple_let : destructured = 5. Proof. reflexivity. Qed.
Example numeric_scope : annotation = 7%N. Proof. reflexivity. Qed.
Example scoped_arguments : scoped_call = 7%N. Proof. reflexivity. Qed.
Example signed : negative = (-2)%Z. Proof. reflexivity. Qed.
Example equality_is_prop : prop_equal. Proof. reflexivity. Qed.
Example equality_is_bool : bool_equal = true. Proof. reflexivity. Qed.
Example core_escape : escape = 6. Proof. reflexivity. Qed.
Example nested_block : nested = 6. Proof. reflexivity. Qed.
Example old_syntax : legacy = 1. Proof. reflexivity. Qed.
Example names_not_keywords : identity_names = 30. Proof. reflexivity. Qed.
Example same_effects : forall c, read_update c =
  bind (read_cell c) (fun n => bind (write_cell c (n+1)) (fun _ => ret n)).
Proof. reflexivity. Qed.
Example same_destructuring : forall c, read_pair c =
  bind (read_cell c) (fun p => let '(a,b) := p in ret (a+b)).
Proof. reflexivity. Qed.
SOMA
soma check "$WORK/blocks.soma" > "$WORK/check.log" 2>&1
# ML spellings remain scoped; a malformed block cannot enable a parser mode.
cat > "$WORK/unscoped.soma" <<'SOMA'
f := fun x -> x.
SOMA
if soma check "$WORK/unscoped.soma" > "$WORK/unscoped.log" 2>&1; then
  echo 'unscoped ML lambda unexpectedly accepted' >&2; exit 1
fi
cat > "$WORK/bad.soma" <<'SOMA'
f := ml { let x = 2 in }.
SOMA
if soma check "$WORK/bad.soma" > "$WORK/bad.log" 2>&1; then
  echo 'malformed block unexpectedly accepted' >&2; exit 1
fi
cat > "$WORK/bad_type.soma" <<'SOMA'
Require Import Sandbox.
f : io nat := ml { let* n = Some 2 in ret n }.
SOMA
if soma check "$WORK/bad_type.soma" > "$WORK/bad_type.log" 2>&1; then
  echo 'let* unexpectedly accepted a non-io value' >&2; exit 1
fi
soma check "$WORK/blocks.soma" > "$WORK/recheck.log" 2>&1
echo 'PASS ML blocks: bindings, hygiene, scopes, matches, lambdas, and exact io lowering'
