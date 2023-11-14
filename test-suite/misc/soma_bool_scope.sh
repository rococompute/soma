#!/usr/bin/env bash

# Regression: bool_scope, previously reached through the prelude, must
# stay open for importing programs now that Reals/QArith/Qreals/Lra are
# opt-in in the prelude (theories/Soma/Soma.v opens it with #[export]).
# A separate importing module uses `&&` (and `||`) without opening
# bool_scope itself, and an explicit Stdlib import of the removed
# libraries must still work.

set -euo pipefail

export PATH=$BIN:$PATH
export SOMA_MIRAGE_BUILD=0
export SOMA_OCAML_BUILD=0

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
export SOMA_CACHE="$TMP/store"

cat > deplib.soma <<'EOF'
both (a b : bool) : bool := a && b.
either (a b : bool) : bool := a || b.
EOF

cat > main.soma <<'EOF'
Import deplib.
checked : bool := both true false || either true false.
checked.
EOF

soma build -v main.soma > out.log 2> err.log || { cat out.log err.log; exit 1; }
grep -q '= true' out.log

cat > noreals.soma <<'EOF'
x : R := sqrt 2.
EOF
if soma build noreals.soma > out.log 2> err.log; then
  echo "R still available without importing Reals"; cat err.log; exit 1
fi
grep -q 'R' err.log

cat > withreals.soma <<'EOF'
From Stdlib Require Import QArith Reals Qreals Lra.
Close Scope Q_scope.
x : R := (sqrt 2)%R.
r : R := Q2R (1 # 2)%Q.
two : nat := 2.
EOF
soma build withreals.soma > out.log 2> err.log || { cat out.log err.log; exit 1; }
