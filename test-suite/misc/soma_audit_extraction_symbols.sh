#!/usr/bin/env bash
# Symbol rule tables are diagnostic only. Both informative instances must
# remain in the extracted IR, and their rule labels must not be lost by an
# empty-instance diagnostic lookup. Kernel rewrite behavior remains distinct.
set -euo pipefail
export PATH="$BIN:$PATH"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cat > "$TMP/rules.v" <<'ROCQ'
From Corelib Require Extraction.
#[universes(polymorphic)] Symbol dispatch@{q;u} : forall {A : Type@{q;u}}, A -> nat.
Rewrite Rule dispatch_rules :=
| dispatch@{SProp;_} _ => 0
| dispatch@{Type;_} _ => 1.
Inductive STrue : SProp := SI.
Goal dispatch SI = 0. Proof. reflexivity. Qed.
Goal dispatch tt = 1. Proof. reflexivity. Qed.
Extraction "symbols" dispatch.
ROCQ
cd "$TMP"
rocq c -q -allow-rewrite-rules rules.v > out.log 2>&1 || { cat out.log; exit 1; }
grep -q 'dispatch_rules' out.log || { cat out.log; echo 'the used symbol lost its rewrite-rule label'; exit 1; }
if grep -q 'dispatch (no rules)' out.log; then cat out.log; exit 1; fi
python3 - <<'PY'
from pathlib import Path
ml = Path('symbols.ml').read_text()
assert ml.count('AXIOM TO BE REALIZED (rules.dispatch)') == 2, ml
print('both informative symbol instances survive; rule warning and kernel reductions agree: ok')
PY
