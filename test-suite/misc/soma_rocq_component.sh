#!/usr/bin/env bash

# A Rocq Library package and version are each one directory under the
# project's cache and, from opam, an argument (SECURITY-REVIEW.md S-2).
# "../" must not leave the cache, and a leading "-" must not reach opam.
# Each of these is refused before a directory is created and before opam
# runs. An ordinary package and version still passes that check.

set -euo pipefail

export PATH="$BIN:$PATH"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
export HOME="$TMP/home"
export XDG_CACHE_HOME="$TMP/xdg"
export SOMA_CACHE="$TMP/store"
unset SOMA_OCAML_SWITCH || true
mkdir -p "$HOME" "$XDG_CACHE_HOME" "$SOMA_CACHE" bin proj/vendor/mylib/theories outside
echo marker > outside/marker

# opam, if reached, only records the arguments. A refused library must
# not run it; an accepted name reaches [opam source] and then stops.
OPAM_LOG="$TMP/opam-calls"
: > "$OPAM_LOG"
cat > bin/opam <<'EOT'
#!/bin/sh
printf '%s\n' "$*" >> "$OPAM_LOG"
case "$1 $2" in
  "switch create"|"repo add") exit 0 ;;
  "repo list") printf 'coq-released\n'; exit 0 ;;
esac
exit 1
EOT
chmod +x bin/opam
export PATH="$TMP/bin:$PATH"
export OPAM_LOG

printf 'Definition two := 2.\n' > proj/vendor/mylib/theories/A.v
printf '(rocq.theory\n (name mylib)\n (package mylib))\n' > proj/vendor/mylib/theories/dune

# Anything written for a library lives under the project's cache. The
# marker outside it, and the rest of this temporary directory aside from
# the sources and the two caches, stay as this script left them.
confined() {
  [ "$(cat outside/marker)" = marker ]
  [ "$(ls -A outside)" = marker ]
  if find "$TMP" -name '*-local-*' -print | grep -q .; then
    echo "a refused package was written on disk ($1)"
    find "$TMP" -name '*-local-*' -print
    exit 1
  fi
}

refused() {
  local label="$1" src="$2" expected="$3"
  : > "$OPAM_LOG"
  printf '%s\n' "$src" > proj/bad.soma
  if soma build proj/bad.soma > out.log 2>&1; then
    echo "accepted: $label"
    cat out.log
    exit 1
  fi
  if ! grep -q -F -- "$expected" out.log; then
    echo "missing error for $label"
    cat out.log
    exit 1
  fi
  if [ -s "$OPAM_LOG" ]; then
    echo "opam was invoked for $label"
    cat "$OPAM_LOG"
    exit 1
  fi
  confined "$label"
}

refused 'package ../x' \
  'Rocq Library "../x" in "vendor/mylib".' \
  'package "../x" is not one safe path component.'
refused 'package beginning with -' \
  'Rocq Library "-evil" in "vendor/mylib".' \
  'package "-evil" is not one safe path component.'
refused 'version containing /' \
  'Rocq Library "foo" "1.2/3".' \
  'version "1.2/3" is not one safe path component.'
refused 'version ..' \
  'Rocq Library "foo" "..".' \
  'version ".." is not one safe path component.'

# foo at 1.2.0 is one safe component each, so the build gets as far as opam
: > "$OPAM_LOG"
printf '%s\n' 'Rocq Library "foo" "1.2.0".' > proj/good.soma
if soma build proj/good.soma > out.log 2>&1; then
  echo "foo 1.2.0 built without a real package"
  cat out.log
  exit 1
fi
if grep -q -F 'is not one safe path component' out.log; then
  echo "foo 1.2.0 was refused"
  cat out.log
  exit 1
fi
grep -q -F 'opam source foo.1.2.0 failed' out.log
grep -q -F 'foo.1.2.0' "$OPAM_LOG"
# the fetch directory is under the cache, and nothing landed outside it
find proj/.soma-cache/rocq -maxdepth 1 -type d -name 'foo.1.2.0-*' | grep -q .
[ "$(cat outside/marker)" = marker ]
[ "$(ls -A outside)" = marker ]
if find "$HOME" -mindepth 1 -print | grep -q .; then
  echo "wrote outside Soma's cache for foo 1.2.0"
  find "$HOME" -mindepth 1 -print
  exit 1
fi
