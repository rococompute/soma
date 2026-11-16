#!/usr/bin/env bash
set -euo pipefail
export PATH="$BIN:$PATH"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
cat > soma.toml <<'EOT'
[project]
name = "record_update_regression"
version = "0.1.0"
EOT
cat > main.soma <<'EOT'
Record state := {
  pc : nat; ticks : nat; a : nat; b : nat; c : nat; d : nat;
  e : nat; f : nat; g : nat; h : nat; i : nat; j : nat
}.
Definition advance (s : state) :=
  {| {| {| s with pc := S (pc s) |} with ticks := S (ticks s) |}
     with a := 0; b := 1; c := 2; d := 3 |}.
Print advance.
Inductive step : state -> state -> Prop :=
| step_advance : forall s, step s (advance s).
EOT
cat > main.exp <<'EOT'
Theorem setters_compute (s : state) : pc (set_pc 7 s) = 7 /\ j (set_pc 7 s) = j s.
Proof. split; reflexivity. Qed.
Theorem invert_step : forall s t, step s t ->
  pc t = S (pc s) /\ ticks t = S (ticks s) /\ j t = j s.
Proof.
  intros s t H. inversion H; subst. unfold advance.
  rewrite !pc_set_d, !pc_set_c, !pc_set_b, !pc_set_a,
    !pc_set_ticks, !pc_set_pc.
  rewrite !ticks_set_d, !ticks_set_c, !ticks_set_b, !ticks_set_a,
    !ticks_set_ticks.
  rewrite !j_set_d, !j_set_c, !j_set_b, !j_set_a,
    !j_set_ticks, !j_set_pc.
  repeat split; reflexivity.
Qed.
EOT
if soma build --help 2>&1 | grep -q -- --timings; then
  soma build --timings main.soma
else
  time soma build main.soma
fi
