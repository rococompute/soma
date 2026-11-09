#!/usr/bin/env bash
# A matching source stamp is not compiler provenance.
set -euo pipefail
export PATH=$BIN:$PATH
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
export SOMA_CACHE="$TMP/shared"
mkdir "$TMP/project"
cd "$TMP/project"
printf 'x : nat := 1.\n' > a.soma
printf 'Import a.\nx.\n' > main.soma
build() { soma build -v main.soma > "$TMP/out" 2> "$TMP/err" || { cat "$TMP/out" "$TMP/err"; exit 1; }; }
build
grep -q '^Compiling a.soma' "$TMP/err"
build
! grep -q '^Compiling' "$TMP/err"
# An unrelated pre-existing file must never be published.
printf 'poison\n' > .soma-cache/unwritten.vo
printf 'Forged %s\n' "$TMP" > .soma-cache/load-paths
rm -rf "$SOMA_CACHE"
build
! find "$SOMA_CACHE" \( -name unwritten.vo -o -name load-paths \) | grep -q .
# Even genuine bytes become untrusted when supplied by the checkout.
git init -q
git add -f .soma-cache/a.vo .soma-cache/a.stamp
build
grep -q '^Compiling a.soma' "$TMP/err"
# Remove tracking and the local cache: an honest shared entry is reusable.
git rm -q --cached -r .soma-cache
rm -rf .soma-cache
build
! grep -q '^Compiling' "$TMP/err"
# Another binary (same program with an extra ELF trailer) has another key.
mkdir "$TMP/bin"
ln -s "$(cd "$BIN/../lib" && pwd)" "$TMP/lib"
cp "$(command -v soma)" "$TMP/bin/soma"
# Dune installations carry their library locations alongside the executable.
if [ -f "$BIN/coq_environment.txt" ]; then
  cp "$BIN/coq_environment.txt" "$TMP/bin/"
fi
chmod u+w "$TMP/bin/soma"
printf '\nsecurity-test-build\n' >> "$TMP/bin/soma"
rm -rf .soma-cache
"$TMP/bin/soma" build -v main.soma > "$TMP/out" 2> "$TMP/err" || { cat "$TMP/out" "$TMP/err"; exit 1; }
grep -q '^Compiling a.soma' "$TMP/err"
[ "$(find "$SOMA_CACHE" -mindepth 1 -maxdepth 1 -type d | wc -l)" -eq 2 ]

# A forged matching stamp cannot authorize an object from another source.
printf 'x : nat := 2.\n' > a.soma
source_digest=$(md5sum a.soma | cut -d ' ' -f 1)
stamp_digest=$(printf '%s - - - - -' "$source_digest" | md5sum | cut -d ' ' -f 1)
sed "s/^source .*/source $stamp_digest/" .soma-cache/a.stamp > a.stamp.new && mv a.stamp.new .soma-cache/a.stamp  # not sed -i: BSD's differs
git add -f .soma-cache/a.vo .soma-cache/a.stamp
build
grep -q '^Compiling a.soma' "$TMP/err"
grep -q '= 2' "$TMP/out"
