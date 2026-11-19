#!/usr/bin/env bash
# A diagnostic flag must not invalidate otherwise identical build products.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
export SOMA_CACHE="$fixture/store"
mkdir "$fixture/project"
cd "$fixture/project"
printf 'value : nat := 42.\n' > leaf.soma
printf 'Import leaf.\nanswer := value.\n' > main.soma

# A genuinely compiled timing run must leave ordinary freshness usable.
soma build --timings main.soma > "$fixture/timed.log" 2>&1
grep -q '^Total: ' "$fixture/timed.log"
if ! soma build --check-fresh main.soma > "$fixture/fresh.log" 2>&1; then
  cat "$fixture/fresh.log"
  echo 'timing reports invalidated ordinary build freshness'
  exit 1
fi

# Both flag spellings reuse the same products, while timing still reports
# the cost of the no-op invocation. No module should be compiled again.
soma build main.soma > "$fixture/plain.log" 2>&1
grep -q 'unchanged since its last build' "$fixture/plain.log"
soma build --timings main.soma > "$fixture/noop.log" 2>&1
grep -q 'unchanged since its last build' "$fixture/noop.log"
grep -q '^Total: ' "$fixture/noop.log"
if grep -q '^Compiling' "$fixture/noop.log"; then
  cat "$fixture/noop.log"
  exit 1
fi
soma build --check-fresh --timings main.soma > "$fixture/fresh-timed.log" 2>&1
grep -qx 'main.soma: unchanged' "$fixture/fresh-timed.log"

# Ignoring diagnostics must not hide a real input edit.
printf 'value : nat := 43.\n' > leaf.soma
if soma build --check-fresh --timings main.soma > "$fixture/edited.log" 2>&1; then
  echo 'timing mode accepted edited source as fresh'
  exit 1
fi
grep -q 'source ./leaf.soma changed' "$fixture/edited.log"
echo 'timing reports preserve build freshness: passed'
