#!/usr/bin/env bash

# soma diff of two folders whose path is not a plain name (vernac/somaDiff.ml):
# the soma.toml made for the purpose names the folder as a TOML basic string,
# so a quote, a backslash, a space or a newline in the path neither ends the
# string nor changes which folder is compared. Before, a path with a ' made
# the file unreadable, and both sides were said not to compile.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
TMP="$(pwd -P)"
export XDG_CACHE_HOME="$TMP/cache"

says() { grep -qF -- "$1" out.log || { echo "expected: $1"; cat out.log; exit 1; }; }
not_says() { if grep -qF -- "$1" out.log; then echo "did not expect: $1"; cat out.log; exit 1; fi; }
under() {
  awk -v s="$1" -v l="  $2" 'index($0, s) == 1 { on = 1; next } /^$/ { on = 0 } on && $0 == l { f = 1 } END { exit !f }' out.log \
    || { echo "expected, under $1: $2"; cat out.log; exit 1; }
}
EDITED='Edited:'

# a project called lib in DIR, whose main is BODY
project() {
  mkdir -p "$1"
  printf '[project]\nname = "lib"\nversion = "1.0.0"\n' > "$1/soma.toml"
  printf '%s\n' "$2" > "$1/main.soma"
}
diff_() { soma diff "$1" "$2" > out.log 2>&1 || { cat out.log; exit 1; }; }
compared() { diff_ "$1" "$2"; under "$EDITED" main.main; not_says 'Not compared'; }
unchanged() { diff_ "$1" "$2"; says '1 unchanged.'; not_says 'Not compared'; }

# * An ordinary path still works, and the folder is compared
project plain-old 'main : nat := 1.'
project plain-new 'main : nat := 2.'
compared "$TMP/plain-old" "$TMP/plain-new"

# * A single quote: the folder is compared, and the same folder is read
project "it's-old" 'main : nat := 1.'
project "it's-new" 'main : nat := 2.'
compared "$TMP/it's-old" "$TMP/it's-new"
project "same'old" 'main : nat := 1.'
project "same'new" 'main : nat := 1.'
unchanged "$TMP/same'old" "$TMP/same'new"

# * A double quote, and both kinds in one path
project 'say"old' 'main : nat := 1.'
project 'say"new' 'main : nat := 2.'
compared "$TMP/say\"old" "$TMP/say\"new"
project "both'\"old" 'main : nat := 1.'
project "both'\"new" 'main : nat := 2.'
compared "$TMP/both'\"old" "$TMP/both'\"new"

# * A backslash names the folder with one backslash, not two: a decoy folder
# whose name has two is not the one compared
project 'back\slash-old' 'main : nat := 1.'
project 'back\slash-new' 'main : nat := 2.'
project 'back\\slash-old' 'decoy : nat := 1.'
compared "$TMP/back\\slash-old" "$TMP/back\\slash-new"
not_says 'decoy'

# * A space
project 'with space-old' 'main : nat := 1.'
project 'with space-new' 'main : nat := 2.'
compared "$TMP/with space-old" "$TMP/with space-new"

# * A newline, and a tab
project $'new\nline-old' 'main : nat := 1.'
project $'new\nline-new' 'main : nat := 2.'
compared "$TMP/"$'new\nline-old' "$TMP/"$'new\nline-new'
project $'tab\there-old' 'main : nat := 1.'
project $'tab\there-new' 'main : nat := 2.'
compared "$TMP/"$'tab\there-old' "$TMP/"$'tab\there-new'

# * What it is checked as, and not run: nothing is written to either folder
[ ! -e "it's-old/soma.lock" ] && [ ! -e "it's-old/.soma-cache" ]
[ "$(ls -A "it's-old" | sort | tr '\n' ' ')" = 'main.soma soma.toml ' ]
