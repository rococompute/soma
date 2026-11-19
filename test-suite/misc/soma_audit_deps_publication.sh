#!/usr/bin/env bash

# Concurrent publication of a dependency's source in the shared cache
# (vernac/somaDeps.ml, fetch). Two builds that start on a cold
# $XDG_CACHE_HOME both fetch the same pinned commit; one moves its folder
# into the cache first. The other must take that folder, whole and of the
# same commit, instead of failing with ENOTEMPTY or taking a partial one.
# A folder published without its marker, or with another commit's, is not
# trusted. A fetch that fails publishes nothing, leaves no work folder, and
# a later build fetches again.
#
# git's url.insteadOf, from the environment (never the global configuration),
# makes https://HOST/ a folder of bare repositories. A git wrapper delays
# fetch, and can plant a folder at the destination, so that the race is
# certain; it changes nothing of soma.

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

# publish HOST/OWNER/REPO TAG: the folder work/HOST/OWNER/REPO, at the tag
publish() {
  local work="$TMP/work/$1" bare="$TMP/remote/$1.git"
  if [ ! -d "$bare" ]; then
    mkdir -p "$bare"; git -C "$bare" init -q --bare
    git -C "$work" init -q; git -C "$work" remote add origin "$bare"
  fi
  git -C "$work" add -A
  git -C "$work" commit -q -m "$2" --allow-empty
  git -C "$work" tag "$2"
  git -C "$work" push -q origin HEAD "refs/tags/$2"
}
# project HOST/OWNER/REPO NAME VERSION: its soma.toml
project() {
  cd "$TMP"
  mkdir -p "$TMP/work/$1"
  printf '[project]\nname = "%s"\nversion = "%s"\n' "$2" "$3" > "$TMP/work/$1/soma.toml"
}
# top DIR: a project of its own that depends on owner/maps 1.0.0
top() {
  mkdir -p "$TMP/$1"
  printf '[project]\nname = "shop"\nversion = "0.1.0"\n\n[dependencies]\n"owner/maps" = "1.0.0"\n' \
    > "$TMP/$1/soma.toml"
  printf 'Import maps.gmap.\ntwice 4.\n' > "$TMP/$1/main.soma"
}
says() { grep -q -- "$1" "${2:-out.log}" || { echo "expected: $1"; cat "${2:-out.log}"; exit 1; }; }
# cold: no source cache, no compiled cache, no soma.lock
cold() { rm -rf "$XDG_CACHE_HOME" "$TMP/a/.soma-cache" "$TMP/b/.soma-cache" "$TMP/a/soma.lock" "$TMP/b/soma.lock"; }
# source: the one folder of the cache, for the pinned commit
source_of() {
  local found
  found="$(find "$XDG_CACHE_HOME/soma/src" -mindepth 1 -maxdepth 4 -type d -name "maps@1.0.0-$COMMIT" 2>/dev/null || true)"
  [ -n "$found" ] || { echo "no source folder for $COMMIT"; find "$XDG_CACHE_HOME" -maxdepth 6; exit 1; }
  [ "$(printf '%s\n' "$found" | wc -l)" = 1 ] || { echo "more than one source folder:"; echo "$found"; exit 1; }
  printf '%s\n' "$found"
}
no_work() { # no folder of a fetch left beside the source
  local left
  left="$(find "$XDG_CACHE_HOME/soma/src" -name '*.tmp-*' 2>/dev/null || true)"
  [ -z "$left" ] || { echo "fetch work folders left behind:"; echo "$left"; exit 1; }
}
# whole SOURCE: the pinned tree, complete, and its marker
whole() {
  local src="$1" f
  [ -d "$src" ] || { echo "no source at $src"; exit 1; }
  [ ! -e "$src/.git" ] || { echo ".git left in $src"; exit 1; }
  [ "$(cat "$src/.soma-source")" = "$COMMIT" ] || { echo "marker is not $COMMIT:"; cat "$src/.soma-source"; exit 1; }
  diff <(git -C "$W" ls-tree -r --name-only v1.0.0 | sort) \
       <(cd "$src" && find . -type f ! -name .soma-source | sed 's|^\./||' | sort) \
    || { echo "the source is not the pinned tree"; exit 1; }
  while read -r f; do
    git -C "$W" show "v1.0.0:$f" | cmp -s - "$src/$f" || { echo "differs from the pin: $f"; exit 1; }
  done < <(git -C "$W" ls-tree -r --name-only v1.0.0)
  [ -z "$(find "$src" -name '*.vo' -o -name '.soma-cache')" ] || { echo "a build wrote into the source"; exit 1; }
}

project github.com/owner/maps maps 1.0.0
cat > work/github.com/owner/maps/gmap.soma <<'EOT'
Import util.
twice (n : nat) : nat := helper n + helper n.
EOT
echo 'helper (n : nat) : nat := n.' > work/github.com/owner/maps/util.soma
publish github.com/owner/maps v1.0.0
W="$TMP/work/github.com/owner/maps"
COMMIT="$(git -C "$W" rev-parse 'v1.0.0^{commit}')"
top a; top b

# git, but slow to fetch, and able to plant a folder where the source goes
REAL_GIT="$(command -v git)"
mkdir -p "$TMP/git"
cat > "$TMP/git/git" <<EOF
#!/bin/sh
for a in "\$@"; do
  case "\$a" in
    fetch)
      sleep "\${SOMA_TEST_FETCH_DELAY:-0}"
      case "\${SOMA_TEST_PLANT:-}" in
        incomplete) mkdir -p "\$SOMA_TEST_PLANT_DIR"; echo partial > "\$SOMA_TEST_PLANT_DIR/partial.soma" ;;
        other) mkdir -p "\$SOMA_TEST_PLANT_DIR"
               printf '%s\n' "\$SOMA_TEST_PLANT_COMMIT" > "\$SOMA_TEST_PLANT_DIR/.soma-source"
               echo other > "\$SOMA_TEST_PLANT_DIR/other.soma" ;;
      esac ;;
  esac
done
exec "$REAL_GIT" "\$@"
EOF
chmod +x "$TMP/git/git"
SLOW="$TMP/git:$PATH"

# * One build on a cold cache publishes the whole pinned source, and no work folder
cold
(cd "$TMP/a" && soma build -v main.soma > "$TMP/a.log" 2>&1) || { cat "$TMP/a.log"; exit 1; }
says '= 8' "$TMP/a.log"
SRC="$(source_of)"; whole "$SRC"; no_work

# * Two builds, one cold source cache: both get the same whole source
# Three rounds, each cold. The wrapper's delay makes the two fetches overlap,
# which is what a cold shared cache does when two builds start together.
for round in 1 2 3; do
  cold
  (cd "$TMP/a" && PATH="$SLOW" SOMA_TEST_FETCH_DELAY=0.3 soma build -v main.soma > "$TMP/a.log" 2>&1) & pa=$!
  (cd "$TMP/b" && PATH="$SLOW" SOMA_TEST_FETCH_DELAY=0.3 soma build -v main.soma > "$TMP/b.log" 2>&1) & pb=$!
  ra=0; wait $pa || ra=$?
  rb=0; wait $pb || rb=$?
  [ $ra = 0 ] || { echo "round $round: a failed ($ra)"; cat "$TMP/a.log"; exit 1; }
  [ $rb = 0 ] || { echo "round $round: b failed ($rb)"; cat "$TMP/b.log"; exit 1; }
  says '= 8' "$TMP/a.log"; says '= 8' "$TMP/b.log"
  says 'Fetching github.com/owner/maps 1.0.0' "$TMP/a.log"
  says 'Fetching github.com/owner/maps 1.0.0' "$TMP/b.log"
  SRC="$(source_of)"; whole "$SRC"; no_work
  # both built from that source, and both pinned the same commit
  [ -n "$(find "$TMP/a/.soma-cache/.deps" -name gmap.vo)" ]
  [ -n "$(find "$TMP/b/.soma-cache/.deps" -name gmap.vo)" ]
  grep -q "commit = \"$COMMIT\"" "$TMP/a/soma.lock"
  grep -q "commit = \"$COMMIT\"" "$TMP/b/soma.lock"
  # the source is there once, and a third build uses it without fetching
  (cd "$TMP/a" && soma build -v main.soma > "$TMP/a.log" 2>&1) || { cat "$TMP/a.log"; exit 1; }
  if grep -q Fetching "$TMP/a.log"; then cat "$TMP/a.log"; echo "fetched a source already there"; exit 1; fi
  says '= 8' "$TMP/a.log"
done

# * A folder that another build published is taken only when it says it is
# whole, and of the commit fetched: a plant without a marker is refused
cold
PLANT="$XDG_CACHE_HOME/soma/src/github.com/owner/maps@1.0.0-$COMMIT"
if (cd "$TMP/a" && PATH="$SLOW" SOMA_TEST_FETCH_DELAY=0.1 SOMA_TEST_PLANT=incomplete \
      SOMA_TEST_PLANT_DIR="$PLANT" soma build -v main.soma > "$TMP/a.log" 2>&1); then
  echo "took a folder with no marker as the source"; cat "$TMP/a.log"; exit 1
fi
says 'may be' "$TMP/a.log"
says 'incomplete' "$TMP/a.log"
says "$PLANT" "$TMP/a.log"
if grep -q 'Directory not empty' "$TMP/a.log"; then cat "$TMP/a.log"; exit 1; fi
no_work
# ... and one whose marker is another commit's
cold
PLANT="$XDG_CACHE_HOME/soma/src/github.com/owner/maps@1.0.0-$COMMIT"
if (cd "$TMP/a" && PATH="$SLOW" SOMA_TEST_FETCH_DELAY=0.1 SOMA_TEST_PLANT=other \
      SOMA_TEST_PLANT_DIR="$PLANT" SOMA_TEST_PLANT_COMMIT=0000000000000000000000000000000000000000 \
      soma build -v main.soma > "$TMP/a.log" 2>&1); then
  echo "took another commit's folder as the source"; cat "$TMP/a.log"; exit 1
fi
says 'the source cache holds 0000000000000000000000000000000000000000' "$TMP/a.log"
says "not the commit $COMMIT" "$TMP/a.log"
no_work
# removing what was refused, the next build publishes the source
rm -rf "$PLANT"
(cd "$TMP/a" && soma build -v main.soma > "$TMP/a.log" 2>&1) || { cat "$TMP/a.log"; exit 1; }
SRC="$(source_of)"; whole "$SRC"; no_work

# * A fetch that fails publishes nothing, leaves no work folder, and a retry works
cold
mv "$TMP/remote" "$TMP/remote.off"
if (cd "$TMP/a" && soma build -v main.soma > "$TMP/a.log" 2>&1); then
  echo "built with no remote"; cat "$TMP/a.log"; exit 1
fi
says 'git failed' "$TMP/a.log"
[ -z "$(find "$XDG_CACHE_HOME/soma/src" -mindepth 1 -maxdepth 4 -type d -name 'maps@*' 2>/dev/null)" ] \
  || { echo "a failed fetch published a source"; find "$XDG_CACHE_HOME/soma/src"; exit 1; }
no_work
mv "$TMP/remote.off" "$TMP/remote"
(cd "$TMP/a" && soma build -v main.soma > "$TMP/a.log" 2>&1) || { cat "$TMP/a.log"; exit 1; }
says 'Fetching github.com/owner/maps 1.0.0' "$TMP/a.log"
SRC="$(source_of)"; whole "$SRC"; no_work

# * A commit the host no longer has: the error says so, and nothing is published
cold
printf '# written by soma\n\n[[resolved]]\npath = "github.com/owner/maps"\nversion = "1.0.0"\ncommit = "%s"\n' \
  0000000000000000000000000000000000000000 > "$TMP/a/soma.lock"
if (cd "$TMP/a" && soma build -v main.soma > "$TMP/a.log" 2>&1); then
  echo "built a commit the host does not have"; cat "$TMP/a.log"; exit 1
fi
says 'is no longer on https://github.com/owner/maps.git' "$TMP/a.log"
says 'soma get writes it' "$TMP/a.log"
[ -z "$(find "$XDG_CACHE_HOME/soma/src" -mindepth 1 -maxdepth 4 -type d -name 'maps@*' 2>/dev/null)" ] \
  || { echo "a failed checkout published a source"; find "$XDG_CACHE_HOME/soma/src"; exit 1; }
no_work
rm -f "$TMP/a/soma.lock"
(cd "$TMP/a" && soma build -v main.soma > "$TMP/a.log" 2>&1) || { cat "$TMP/a.log"; exit 1; }
SRC="$(source_of)"; whole "$SRC"; no_work
