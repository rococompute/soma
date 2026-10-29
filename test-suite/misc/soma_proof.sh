#!/usr/bin/env bash

# A Soma program FILE.soma has its lemmas and theorems in
# FILE.proof, read after it in its environment (toplevel/ccompile.ml):
# a proof that does not hold fails the build, with its location in
# FILE.proof.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

# the program imports Arith; the proofs use it without importing it
cat > double.soma <<'EOT'
Require Import Stdlib.Arith.Arith.
Definition double n := n + n.
EOT

cat > double.proof <<'EOT'
Theorem double_twice : forall n, double n = 2 * n.
Proof. intros n. unfold double. simpl. now rewrite Nat.add_0_r. Qed.
EOT

rocq c -q double.soma
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
if rocq c -q double.soma > out.log 2>&1; then
  echo "a false theorem in double.proof did not fail the build"; exit 1
fi
grep -q 'File "./double.proof", line 4' out.log
[ ! -f double.vo ]

# without a .proof file, nothing more is read
rm double.proof
rocq c -q double.soma

# proofs are only in .proof files: a .soma (or .lang) file cannot start
# one, whether with Theorem or with a definition proved interactively
fails() { # fails FILE: compiling FILE fails, as it starts a proof
  if rocq c -q "$1" > out.log 2>&1; then
    echo "$1 was accepted"; exit 1
  fi
  grep -q "Proofs go in a .proof file" out.log || { cat out.log; exit 1; }
}
printf 'Theorem t : 1 = 1.\nProof. reflexivity. Qed.\n' > theorem.soma
fails theorem.soma
printf 'Definition d : nat.\nProof. exact 0. Defined.\n' > interactive.soma
fails interactive.soma
printf 'Lemma l : True.\nProof. exact I. Qed.\n' > lemma.lang
fails lemma.lang
# Rocq's .v files keep theirs
printf 'Theorem t : 1 = 1.\nProof. reflexivity. Qed.\n' > theorem.v
rocq c -q theorem.v

# .proof files have the proof sentences of theories/Soma/Proof.v, which
# check what they state
cat > double.proof <<'EOT'
Theorem double_bigger : forall n : nat, n > 0 -> double n > n.
Proof.
  Take n : nat.
  Assume that n > 0 as n_pos.
  We need to show that n + n > n.
  We conclude that n + n > n.
Qed.
EOT
rm -f double.vo
rocq c -q double.soma
claim_fails() { # claim_fails SENTENCE MESSAGE: a proof with SENTENCE fails
  printf 'Theorem t : forall n : nat, n > 0 -> double n > n.\nProof.\n  Take n : nat.\n  Assume that n > 0 as n_pos.\n  %s\nAdmitted.\n' "$1" > double.proof
  if rocq c -q double.soma > out.log 2>&1; then
    echo "$1 was accepted"; exit 1
  fi
  grep -q "$2" out.log || { cat out.log; exit 1; }
}
claim_fails 'We need to show that n + n > n + 1.' 'The goal is (double n > n) and not (n + n > n + 1)'
claim_fails 'It holds that n > 1 as n_big.' 'This does not follow'
claim_fails 'Take m : nat.' 'No product'
# the sentences are only in .proof files
printf 'Definition We := 1.\n' > names.soma
rocq c -q names.soma
# nothing is left next to the program by lia or nia
[ ! -e .lia.cache ] && [ ! -e .nia.cache ]
