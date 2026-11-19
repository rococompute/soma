#!/usr/bin/env bash
# Explicit -admit roots must populate the dependency graph even when they
# are not reachable from another command-line root. Checking precedence
# and normal dependency validation must remain unchanged.
set -eu
export PATH="$BIN:$PATH"
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

cat > "$d/AdmitBase.v" <<'EOF'
Unset Elimination Schemes.
Inductive bit : Set := on | off.
Definition chosen : bit := on.
EOF
cat > "$d/AdmitLeaf.v" <<'EOF'
Require Import AdmitBase.
Definition chosen_again : bit := chosen.
EOF
cat > "$d/CheckOther.v" <<'EOF'
Unset Elimination Schemes.
Inductive independent : Set := item.
EOF
cat > "$d/CheckClient.v" <<'EOF'
Require Import AdmitLeaf.
Definition client_value : AdmitBase.bit := chosen_again.
EOF
for unit in AdmitBase AdmitLeaf CheckOther CheckClient; do
  rocq c -q -noinit -native-compiler no -R "$d" "" "$d/$unit.v"
done

check_log() {
  local name=$1
  shift
  if ! rocqchk -R "$d" "" "$@" > "$d/$name.log" 2>&1; then
    cat "$d/$name.log" >&2
    echo "FAILURE: rocqchk $name failed" >&2
    exit 1
  fi
}
expect() {
  grep -Fq "$2" "$d/$1.log" || {
    cat "$d/$1.log" >&2
    echo "FAILURE: $1 did not report $2" >&2
    exit 1
  }
}
reject() {
  if grep -Fq "$2" "$d/$1.log"; then
    cat "$d/$1.log" >&2
    echo "FAILURE: $1 unexpectedly reported $2" >&2
    exit 1
  fi
}

# This used to raise missing-dep anomaly 129 before admitting anything.
check_log only -admit AdmitLeaf
expect only 'Admitting library: AdmitBase'
expect only 'Admitting library: AdmitLeaf'
reject only 'Checking library:'

# Previously the unrelated admit closure was likewise absent from depgraph.
check_log unrelated CheckOther -admit AdmitLeaf
expect unrelated 'Checking library: CheckOther'
expect unrelated 'Admitting library: AdmitBase'
expect unrelated 'Admitting library: AdmitLeaf'

# Explicit checked/norec roots always override admission for the root itself.
check_log explicit AdmitLeaf -admit AdmitLeaf
expect explicit 'Checking library: AdmitLeaf'
expect explicit 'Admitting library: AdmitBase'
reject explicit 'Admitting library: AdmitLeaf'
check_log overlap AdmitBase -admit AdmitLeaf
expect overlap 'Checking library: AdmitBase'
expect overlap 'Admitting library: AdmitLeaf'
reject overlap 'Admitting library: AdmitBase'
check_log norec -norec AdmitLeaf -admit AdmitLeaf
expect norec 'Checking library: AdmitLeaf'
expect norec 'Admitting library: AdmitBase'
reject norec 'Admitting library: AdmitLeaf'

# Ordinary checking remains recursive; explicitly admitted dependencies remain
# admitted when the root itself is checked.
check_log normal CheckClient
expect normal 'Checking library: AdmitBase'
expect normal 'Checking library: AdmitLeaf'
expect normal 'Checking library: CheckClient'
reject normal 'Admitting library:'
check_log shared CheckClient -admit AdmitLeaf
expect shared 'Admitting library: AdmitBase'
expect shared 'Admitting library: AdmitLeaf'
expect shared 'Checking library: CheckClient'

# Basic dependency identity/integrity failures must still fail; admitting a
# closure cannot make a missing file or inconsistent dependency disappear.
mv "$d/AdmitBase.vo" "$d/base.saved"
if rocqchk -R "$d" "" -admit AdmitLeaf > "$d/missing.log" 2>&1; then
  echo 'FAILURE: admitted library with a missing dependency was accepted' >&2
  exit 1
fi
if grep -Fq 'Anomaly' "$d/missing.log"; then
  cat "$d/missing.log" >&2
  echo 'FAILURE: missing dependency caused an internal anomaly' >&2
  exit 1
fi
mv "$d/base.saved" "$d/AdmitBase.vo"
printf 'not a compiled library' > "$d/AdmitBase.vo"
if rocqchk -R "$d" "" -admit AdmitLeaf > "$d/corrupt.log" 2>&1; then
  echo 'FAILURE: admitted library with a corrupt dependency was accepted' >&2
  exit 1
fi
echo 'rocqchk admit-only/unrelated closures, explicit precedence and normal validation: passed'
