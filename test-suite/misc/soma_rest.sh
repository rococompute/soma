#!/usr/bin/env bash

# [The rest follows.] (theories/Soma/Proof.v, plugins/soma_proof) searches
# for the rest of a proof and reports it as sentences, which soma build
# mentions, soma build -v prints and soma build --fill writes in its place;
# a search that fails reports what is still to show, as sentences.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

cat > prog.soma <<'EOT'
square (n : nat) := n * n.
pow4 (x : nat) := square (square x).
EOT

cat > prog.proof <<'EOT'
(* The rest follows. in a comment is not a sentence *)
Theorem pow4_is_pow : forall x : nat, pow4 x = x ^ 4.
Proof.
  The rest follows.
Qed.

Theorem mul_swap : forall a b : nat, a * b = b * a.
Proof.
  Take a : nat.
  The rest follows.
Qed.
EOT

# soma build: the proofs are found and mentioned
soma build prog.soma > out.log
grep -q 'prog.proof: 2 proofs found by "The rest follows."' out.log

# soma build -v: printed, as sentences
soma build -v prog.soma > out.log
grep -q '^The rest follows, by:$' out.log
grep -q '^    Take x : nat.$' out.log
grep -q '^    We need to show that square (square x) = x ^ 4.$' out.log
grep -q '^    Take b : nat.$' out.log

# soma build --fill: written in, indented as the sentence; the comment is kept
soma build --fill prog.soma > out.log
grep -q 'prog.proof: 2 proofs written in' out.log
! grep -q '^  The rest follows\.$' prog.proof
grep -q '^  Take x : nat\.$' prog.proof
grep -q 'The rest follows. in a comment' prog.proof
# and the proofs written in check by themselves
soma build prog.soma > out.log
! grep -q 'found by' out.log

# a search that fails reports what is still to show, and fails the build;
# --fill still writes the proofs found before it
cat > prog.proof <<'EOT'
Lemma plus_zero : forall n : nat, n + 0 = n.
Proof.
  The rest follows.
Qed.

Lemma false : forall n : nat, n + 1 = n.
Proof.
  The rest follows.
Qed.
EOT
if soma build --fill prog.soma > out.log 2> err.log; then
  echo "a failing search did not fail the build"; exit 1
fi
grep -q 'prog.proof: 1 proof written in' out.log
grep -q 'Take n : nat.' prog.proof
grep -q 'The rest does not follow. Still to show:' err.log
grep -q 'We need to show that n + 1 = n.' err.log
[ ! -e .lia.cache ] && [ ! -e .nia.cache ]
