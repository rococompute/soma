#!/usr/bin/env bash

# A commit in soma.lock becomes a folder name for the fetched source and
# for what it compiles to, and reaches git (SECURITY-REVIEW.md S-3). It is
# taken only when it is a full commit: exactly 40 hexadecimal digits
# (0-9, a-f). Anything else is refused by read_lock, before a cache or
# source folder is removed or created and before git runs: the folder the
# dependency's source would have lived in, marker and all, stays.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'chmod -R u+w "$TMP"; rm -rf "$TMP"' EXIT
cd "$TMP"
TMP="$(pwd -P)"
export XDG_CACHE_HOME="$TMP/cache"
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0="url.file://$TMP/remote/.insteadOf" GIT_CONFIG_VALUE_0=https://
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t

# git, when reached, is the real one, but says so: a refused lock runs none
REAL_GIT="$(command -v git)"
GIT_LOG="$TMP/git-calls"
: > "$GIT_LOG"
mkdir -p bin
cat > bin/git <<EOT
#!/bin/sh
printf '%s\n' "\$*" >> "$GIT_LOG"
exec "$REAL_GIT" "\$@"
EOT
chmod +x bin/git
export PATH="$TMP/bin:$PATH"
export GIT_LOG

DEPSRC="$XDG_CACHE_HOME/soma/src/github.com/owner/maps@1.0.0-"

top() {
  rm -rf "$TMP/top"; mkdir "$TMP/top"; cd "$TMP/top"
  printf '[project]\nname = "shop"\nversion = "0.1.0"\n\n[dependencies]\n"owner/maps" = "1.0.0"\n' > soma.toml
  printf 'Import maps.gmap.\ntwice 4.\n' > main.soma
}
lock() { # COMMIT: a soma.lock pinning owner/maps 1.0.0 at it
  printf '# written by soma\n\n[[resolved]]\npath = "github.com/owner/maps"\nversion = "1.0.0"\ncommit = "%s"\n' "$1" > soma.lock
}
refused() { # COMMIT: refused for it, naming the dependency and the value
  top; lock "$1"
  mkdir -p "$DEPSRC$1"; echo marker > "$DEPSRC$1/marker"
  : > "$GIT_LOG"
  if soma build main.soma > out.log 2>&1; then
    echo "commit $1 was taken"; cat soma.lock out.log; exit 1
  fi
  grep -q -F 'github.com/owner/maps' out.log || { echo "the error does not name the dependency ($1)"; cat out.log; exit 1; }
  grep -q -F "commit \"$1\"" out.log || { echo "the error does not name commit $1"; cat out.log; exit 1; }
  grep -q -F '40 hexadecimal digits' out.log || { echo "the error does not say what a commit is ($1)"; cat out.log; exit 1; }
  [ "$(cat "$DEPSRC$1/marker")" = marker ] || { echo "the folder for commit $1 was replaced"; exit 1; }
  if [ -s "$GIT_LOG" ]; then echo "git ran for commit $1"; cat "$GIT_LOG"; exit 1; fi
  rm -rf "$DEPSRC$1"
}

refused 'abc1234'
refused 'main'
refused '-evil'
refused '../../evil'

# * A valid 40-digit commit passes validation, and is what is built
cd "$TMP"
mkdir -p work/github.com/owner/maps remote
cat > work/github.com/owner/maps/soma.toml <<'EOT'
[project]
name = "maps"
version = "1.0.0"
EOT
cat > work/github.com/owner/maps/gmap.soma <<'EOT'
Import util.
twice (n : nat) : nat := helper n + helper n.
EOT
echo 'helper (n : nat) : nat := n.' > work/github.com/owner/maps/util.soma
git -C work/github.com/owner/maps init -q
mkdir -p remote/github.com/owner
git init -q --bare remote/github.com/owner/maps.git
git -C work/github.com/owner/maps remote add origin "$TMP/remote/github.com/owner/maps.git"
git -C work/github.com/owner/maps add -A
git -C work/github.com/owner/maps commit -q -m maps
git -C work/github.com/owner/maps tag v1.0.0
git -C work/github.com/owner/maps push -q origin HEAD refs/tags/v1.0.0
COMMIT="$(git -C work/github.com/owner/maps rev-parse HEAD)"
[ "${#COMMIT}" = 40 ] && [ -z "$(printf '%s' "$COMMIT" | tr -d '0-9a-f')" ] || { echo "test bug: $COMMIT is not 40 hex digits"; exit 1; }
top; lock "$COMMIT"
soma build -v main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q -F '= 8' out.log || { echo "the locked commit was not built"; cat out.log; exit 1; }
