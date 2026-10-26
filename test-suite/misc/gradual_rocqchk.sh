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
Definition succ_dyn (x : Dyn) : nat := x + 1.
Lemma ok : succ_dyn 41 = 42. Proof. reflexivity. Qed.
Lemma bad : succ_dyn true = raise. Proof. reflexivity. Qed.
EOT

rocq c -q -Q . Test uses_gradual.v
rocqchk -silent -Q . Test -norec Corelib.Gradual.Gradual -norec Test.uses_gradual
