#!/usr/bin/env bash

# A Lightlang program FILE.light has its lemmas and theorems in
# FILE.proof, read after it in its environment (toplevel/ccompile.ml):
# a proof that does not hold fails the build, with its location in
# FILE.proof.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

# the program imports Arith; the proofs use it without importing it
cat > double.light <<'EOT'
Require Import Stdlib.Arith.Arith.
Definition double n := n + n.
EOT

cat > double.proof <<'EOT'
Theorem double_twice : forall n, double n = 2 * n.
Proof. intros n. unfold double. simpl. now rewrite Nat.add_0_r. Qed.
EOT

rocq c -q double.light
# the theorem is part of the program's library
cat > use.v <<'EOT'
Require double.
Check double.double_twice.
EOT
rocq c -q -Q . "" use.v

# a false theorem fails the build, located in double.proof
cat >> double.proof <<'EOT'
Theorem double_one : double 1 = 3.
Proof. reflexivity. Qed.
EOT
rm -f double.vo
if rocq c -q double.light > out.log 2>&1; then
  echo "a false theorem in double.proof did not fail the build"; exit 1
fi
grep -q 'File "./double.proof", line 4' out.log
[ ! -f double.vo ]

# without a .proof file, nothing more is read
rm double.proof
rocq c -q double.light
