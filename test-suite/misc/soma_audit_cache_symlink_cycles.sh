#!/usr/bin/env bash
# A cyclic source symlink is walked by project_cache_key (topbin/soma.ml).
# With a source suffix (loop.soma -> .) the walk recursed until the kernel
# reported ELOOP and Digest.file raised Sys_error, so even `soma build`
# exited 2. A cycle without a suffix was walked 41 levels before being
# skipped, and a self-referential link failed at stat. All of them must
# leave the build working, must terminate, and must not disturb the key
# of an unchanged project.
set -euo pipefail

export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
TMP="$(mktemp -d)"
export SOMA_CACHE="$TMP/store"
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$TMP/project" "$SOMA_CACHE"
cd "$TMP/project"

printf 'x : nat := 1.\n' > a.soma
printf 'Import a.\nx.\n' > main.soma

build() {
  soma build -v main.soma > "$TMP/out" 2> "$TMP/err" || {
    echo "soma build failed: $1"
    cat "$TMP/out" "$TMP/err"
    exit 1
  }
  # The value is still computed, so the build is real and not an early exit.
  grep -q '= 1' "$TMP/out" || { echo "no value: $1"; cat "$TMP/out" "$TMP/err"; exit 1; }
  ! grep -q 'Too many levels of symbolic links' "$TMP/err" ||
    { echo "ELOOP: $1"; cat "$TMP/err"; exit 1; }
}
compiled() { grep -c '^Compiling' "$TMP/err" || true; }
stored() { find "$SOMA_CACHE" -mindepth 1 -maxdepth 1 -type d | wc -l | tr -d ' '; }

# One key, one compilation: the reference point for the cycles below.
build 'plain project'
[ "$(compiled)" -ge 1 ]
[ "$(stored)" -eq 1 ]

# A directory cycle with a source suffix: it contains no new source bytes,
# so the key, the store and the compilation are those of the plain project.
ln -s . loop.soma
build 'loop.soma -> .'
[ "$(compiled)" -eq 0 ]
[ "$(stored)" -eq 1 ]

# The same project again: a cycle does not make the key unstable.
build 'loop.soma -> . repeated'
[ "$(compiled)" -eq 0 ]
[ "$(stored)" -eq 1 ]

# A cycle without a source suffix: walked before the fix, then skipped.
ln -s . loop
build 'loop -> .'
[ "$(compiled)" -eq 0 ]
[ "$(stored)" -eq 1 ]

# A cycle that is not the root, reached from a subdirectory.
mkdir -p sub
printf 's : nat := 2.\n' > sub/s.soma
ln -s .. sub/up
build 'sub/up -> ..'
[ "$(compiled)" -eq 0 ]          # nothing imported changed
[ "$(stored)" -eq 2 ]            # sub/s.soma is in the key
build 'sub/up -> .. repeated'
[ "$(compiled)" -eq 0 ]
[ "$(stored)" -eq 2 ]

# A link that cannot even be stat'ed: it contributes a marker, not a raise.
ln -s self.soma self.soma
build 'self.soma -> self.soma'
[ "$(stored)" -eq 3 ]
build 'self.soma -> self.soma repeated'
[ "$(compiled)" -eq 0 ]
[ "$(stored)" -eq 3 ]

echo 'soma project cache symlink cycles: passed'
