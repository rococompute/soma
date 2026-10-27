#!/usr/bin/env bash

# rocqchk validates Corelib.Gradual.Gradual itself (the axioms and their
# registration as gradual primitives) and a file whose proofs hold by the
# gradual reduction rules, without admitting either.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

cat > uses_gradual.v <<'EOT'
From Corelib.Gradual Require Import Gradual.
Definition succ_dyn (x : Any) : nat := x + 1.
Lemma ok : succ_dyn 41 = 42. Proof. reflexivity. Qed.
Lemma bad : succ_dyn true = raise. Proof. reflexivity. Qed.
EOT

rocq c -q -Q . Test uses_gradual.v
rocqchk -silent -Q . Test -norec Corelib.Gradual.Gradual -norec Test.uses_gradual

# -gradual-steps bounds gradual reduction per declaration (none by default):
# this proof takes a few dozen steps.
cat > many_steps.v <<'EOT'
From Corelib.Gradual Require Import Gradual.
Definition l : list Any := @cons Any 1 (@cons Any 2 (@cons Any 3 (@cons Any 4 (@cons Any 5 nil)))).
Lemma cast_list : (l : list nat) = cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))).
Proof. reflexivity. Qed.
EOT
rocq c -q -Q . Test many_steps.v
rocqchk -silent -Q . Test -norec Test.many_steps
rocqchk -silent -gradual-steps 100000 -Q . Test -norec Test.many_steps
if rocqchk -silent -gradual-steps 10 -Q . Test -norec Test.many_steps > out.txt 2>&1; then
  echo "rocqchk -gradual-steps 10 should have failed"; exit 1
fi
grep -q "Gradual reduction exceeded 10 steps" out.txt
