#!/usr/bin/env bash

# Theorems proved in Lean (plugins/soma_lean): FILE.definition, next to
# FILE.lean, declares them about Soma's definitions, which Soma translates
# to Lean; Lean checks each before Soma takes it, and refuses sorry.
# Skipped without lean (elan).

set -euo pipefail

export PATH=$BIN:$PATH

command -v elan > /dev/null || { echo "no elan: skipped"; exit 0; }
TOOLCHAIN="$(elan toolchain list | grep -v '^$' | head -1 | cut -d' ' -f1)"
[ -n "$TOOLCHAIN" ] || { echo "no Lean toolchain: skipped"; exit 0; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
export XDG_CACHE_HOME="$TMP/cache"
echo "$TOOLCHAIN" > lean-toolchain

cat > defs.soma <<'EOT'
Fixpoint double (n : nat) : nat := match n with 0 => 0 | Succ m => Succ (Succ (double m)) end.
EOT
cat > facts.definition <<'EOT'
Import defs.
double_is : forall n, double n = 2 * n.
EOT
cat > facts.lean <<'EOT'
import Soma
theorem double_is : ∀ n, Soma.defs.double n = 2 * n := by
  intro n; induction n with
  | zero => rfl
  | succ m ih => simp only [Soma.defs.double, ih]; omega
EOT
cat > main.soma <<'EOT'
Import defs facts.
EOT
cat > main.exp <<'EOT'
Theorem double_even : forall n, Nat.even (double n) = true.
Proof.
  Take n : nat.
  By double_is, it holds that double n = 2 * n as d.
  rewrite d. apply Nat.even_spec. exists n. lia.
Qed.
EOT
soma build main.soma > out.log 2>&1 || { cat out.log; exit 1; }
soma explore main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q "proved in Lean, by facts.lean's double_is" out.log

# what Lean proves is not what is declared
sed -i.bak 's/double n = 2 \* n/double n = 3 * n/' facts.definition
if soma build main.soma > out.log 2>&1; then echo "a statement Lean does not prove was taken"; exit 1; fi
grep -q 'facts.lean does not prove what facts.definition declares' out.log
mv facts.definition.bak facts.definition

# sorry proves nothing
sed -i.bak 's/  intro n; induction n with/  sorry/; /zero =>/d; /succ m ih/d' facts.lean
if soma build main.soma > out.log 2>&1; then echo "sorry was taken"; exit 1; fi
grep -q 'is proved with sorry' out.log
