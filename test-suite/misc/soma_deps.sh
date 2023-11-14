#!/usr/bin/env bash

# A project's dependencies (vernac/somaDeps.ml): other Soma projects, fetched
# from git by tag, selected, locked in soma.lock, and imported by their names.
# git's url.insteadOf makes https://HOST/ a folder of bare repositories.

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

# publish HOST/OWNER/REPO TAG [-a]: the folder work/HOST/OWNER/REPO, at the tag
publish() {
  local work="$TMP/work/$1" bare="$TMP/remote/$1.git"
  if [ ! -d "$bare" ]; then
    mkdir -p "$bare"; git -C "$bare" init -q --bare
    git -C "$work" init -q; git -C "$work" remote add origin "$bare"
  fi
  git -C "$work" add -A
  git -C "$work" commit -q -m "$2" --allow-empty
  if [ "${3-}" = -a ]; then git -C "$work" tag -a -m "$2" "$2"; else git -C "$work" tag "$2"; fi
  git -C "$work" push -q origin HEAD "refs/tags/$2"
}
# project HOST/OWNER/REPO NAME VERSION [DEPENDENCY LINES]: its soma.toml
project() {
  cd "$TMP"
  mkdir -p "$TMP/work/$1"
  printf '[project]\nname = "%s"\nversion = "%s"\n' "$2" "$3" > "$TMP/work/$1/soma.toml"
  if [ -n "${4-}" ]; then printf '\n[dependencies]\n%s\n' "$4" >> "$TMP/work/$1/soma.toml"; fi
}
# top [DEPENDENCY LINES]: a new project in top/, with its main.soma to write
top() {
  rm -rf "$TMP/top"; mkdir "$TMP/top"; cd "$TMP/top"
  printf '[project]\nname = "shop"\nversion = "0.1.0"\n' > soma.toml
  if [ -n "${1-}" ]; then printf '\n[dependencies]\n%s\n' "$1" >> soma.toml; fi
}
ok() { soma build -v "${1:-main.soma}" > out.log 2>&1 || { cat out.log; exit 1; }; }
refused() {
  if soma run main.soma > out.log 2>&1; then echo "was taken, expected: $1"; cat soma.toml main.soma; exit 1; fi
  grep -q -- "$1" out.log || { echo "expected: $1"; cat out.log; exit 1; }
}
says() { grep -q -- "$1" "${2:-out.log}" || { echo "expected: $1"; cat "${2:-out.log}"; exit 1; }; }

# * A dependency, imported by its [project] name
project github.com/owner/maps maps 1.0.0
cat > work/github.com/owner/maps/gmap.soma <<'EOT'
Import util.
twice (n : nat) : nat := helper n + helper n.
EOT
echo 'helper (n : nat) : nat := n.' > work/github.com/owner/maps/util.soma
publish github.com/owner/maps v1.0.0

top '"owner/maps" = "1.0.0"'
printf 'Import maps.gmap.\ntwice 4.\n' > main.soma
ok; says "= 8"
says 'path = "github.com/owner/maps"' soma.lock
says 'version = "1.0.0"' soma.lock
grep -q '^commit = "[0-9a-f]\{40\}"$' soma.lock || { cat soma.lock; exit 1; }
SOURCE="$(ls -d "$XDG_CACHE_HOME"/soma/src/github.com/owner/maps@1.0.0-*)"
[ ! -e "$SOURCE/.git" ]
# nothing of the build goes into the source, which projects share
[ -z "$(find "$SOURCE" -name '*.vo' -o -name '.soma-cache')" ]
[ -n "$(find .soma-cache/.deps -name 'gmap.vo')" ]

# soma.lock is enough: the same build, without the network
mv "$TMP/remote" "$TMP/remote.off"
touch main.soma; ok; says "= 8"
mv "$TMP/remote.off" "$TMP/remote"

# a project's util, and a dependency's, and another's, are three libraries
project github.com/owner/other other 1.0.0
echo 'helper (n : nat) : nat := 100 + n.' > work/github.com/owner/other/util.soma
publish github.com/owner/other v1.0.0
top '"owner/maps" = "1.0.0"
"owner/other" = "1.0.0"'
echo 'own (n : nat) : nat := 1000 + n.' > util.soma
cat > main.soma <<'EOT'
Import maps.gmap.
Import other.util.
Import util.
twice 4.
other.util.helper 1.
own 1.
EOT
ok; says "= 8"; says "= 101"; says "= 1001"

# Import of a name no file has says what there is
top '"owner/maps" = "1.0.0"'
echo 'Import maps.nope.' > main.soma
refused 'maps is github.com/owner/maps, which has no nope.soma'
says 'Import maps.gmap. Its root has gmap, util.'
echo 'Import maps.' > main.soma
refused 'which has no maps.soma'

# * An annotated tag is its commit; a tag without v is a version too
project github.com/owner/ann ann 1.0.0
echo 'one : nat := 1.' > work/github.com/owner/ann/a.soma
publish github.com/owner/ann v1.0.0 -a
project gitlab.com/group/sub/plain plain 2.5.0
echo 'two : nat := 2.' > work/gitlab.com/group/sub/plain/p.soma
publish gitlab.com/group/sub/plain 2.5.0
project github.com/owner/ann ann 2.0.0
echo 'one : nat := 22.' > work/github.com/owner/ann/a.soma
publish github.com/owner/ann v2.0.0
top '"owner/ann" = "1.0.0"
"gitlab.com/group/sub/plain/v2" = "2.5.0"'
printf 'Import ann.a.\nImport plain.p.\none + two.\n' > main.soma
ok; says "= 3"
says "$(git -C "$TMP/work/github.com/owner/ann" rev-parse 'v1.0.0^{commit}')" soma.lock

# no such tag; no soma.toml; a bad soma.toml; two tags for one version
top '"owner/maps" = "9.9.9"'
echo 'Import maps.gmap.' > main.soma
top '"owner/maps" = "1.9.9"'
echo 'Import maps.gmap.' > main.soma
refused 'github.com/owner/maps 1.9.9: no tag v1.9.9 or 1.9.9 on https://github.com/owner/maps.git'
cd "$TMP"; mkdir -p work/github.com/owner/bare; echo x > work/github.com/owner/bare/README
publish github.com/owner/bare v1.0.0
top '"owner/bare" = "1.0.0"'; echo '1.' > main.soma
refused 'the repository has no soma.toml'
project github.com/owner/badname My-shop 1.0.0
publish github.com/owner/badname v1.0.0
top '"owner/badname" = "1.0.0"'; echo '1.' > main.soma
refused 'github.com/owner/badname soma.toml:2: "My-shop" is no project name'
project github.com/owner/twotags twotags 1.0.0
publish github.com/owner/twotags v1.0.0
publish github.com/owner/twotags 1.0.0
top '"owner/twotags" = "1.0.0"'; echo '1.' > main.soma
refused 'are two commits'

# * Selection: the greatest asked for
project github.com/owner/c c 1.0.0; echo 'v : nat := 10.' > work/github.com/owner/c/c.soma
publish github.com/owner/c v1.0.0
project github.com/owner/c c 1.2.0; echo 'v : nat := 12.' > work/github.com/owner/c/c.soma
publish github.com/owner/c v1.2.0
project github.com/owner/a a 1.0.0 '"owner/c" = "1.0.0"'
printf 'Import c.c.\nfrom_a : nat := v.\n' > work/github.com/owner/a/a.soma
publish github.com/owner/a v1.0.0
project github.com/owner/b b 1.0.0 '"owner/c" = "1.2.0"'
printf 'Import c.c.\nfrom_b : nat := v.\n' > work/github.com/owner/b/b.soma
publish github.com/owner/b v1.0.0
top '"owner/a" = "1.0.0"
"owner/b" = "1.0.0"'
printf 'Import a.a.\nImport b.b.\nfrom_a + from_b.\n' > main.soma
ok; says "= 24"
says 'path = "github.com/owner/c"' soma.lock
says 'version = "1.2.0"' soma.lock
# what a dependency asks for is not this project's to import, in any way of
# naming it, and when importing the dependency has already loaded it
top '"owner/a" = "1.0.0"'
for program in 'Import c.c.' 'Require c.c.' 'From c Require Import c.' 'From c Require c.' \
               'Import a.a.
Import c.c.' 'Import a.a.
Import c.' 'Import a.a.
Require c.c.' 'Import a.a.
Require Import c.c.' 'Import a.a.
From c Require Import c.'; do
  echo "$program" > main.soma
  refused 'c is github.com/owner/c, a dependency of a dependency'
  says '"github.com/owner/c" = "1.0.0"'
done
# inside the dependency, it is direct; and naming it makes it this project's
top '"owner/a" = "1.0.0"
"owner/c" = "1.2.0"'
printf 'Import a.a.\nImport c.c.\nv.\n' > main.soma
ok; says "= 12"
# a module of this project's own may have that name
top '"owner/a" = "1.0.0"'
printf 'Import a.a.\nModule c.\nDefinition own := 3.\nEnd c.\nImport c.\nown.\n' > main.soma
ok; says "= 3"
# this project's own line wins, but not below what they ask for
top '"owner/b" = "1.0.0"
"owner/c" = "1.0.0"'
echo 'Import b.b.' > main.soma
refused 'soma.toml:7: "owner/c" is "1.0.0" here, and "1.2.0" in github.com/owner/b. "owner/c" = "1.2.0"'
top '"owner/a" = "1.0.0"
"owner/c" = "1.2.0"'
printf 'Import a.a.\nfrom_a.\n' > main.soma
ok; says "= 12"

# a soma.toml that moves past its soma.lock resolves again; a stale entry goes
sed -i.bak '/owner\/a/d' soma.toml
printf 'Import c.c.\nv.\n' > main.soma
ok; says "= 12"
if grep -q owner/a soma.lock; then cat soma.lock; exit 1; fi
# no dependencies left, no soma.lock left
sed -i.bak '/owner\/c/d' soma.toml
echo '1.' > main.soma
ok; [ ! -e soma.lock ]

# * What cannot be selected
project github.com/owner/x x 1.0.0 '"owner/y" = "1.0.0"'
publish github.com/owner/x v1.0.0
project github.com/owner/y y 1.0.0 '"owner/x" = "1.0.0"'
publish github.com/owner/y v1.0.0
top '"owner/x" = "1.0.0"'; echo '1.' > main.soma
refused 'Dependency cycle: github.com/owner/x -> github.com/owner/y -> github.com/owner/x.'
project github.com/elsewhere/maps maps 1.0.0
publish github.com/elsewhere/maps v1.0.0
top '"owner/maps" = "1.0.0"
"elsewhere/maps" = "1.0.0"'; echo '1.' > main.soma
refused 'is named maps, and so is'
top '"owner/maps" = "1.0.0"'; mkdir maps; echo '1.' > main.soma
refused 'soma.toml:6: the dependency github.com/owner/maps is named maps, and this project has maps/'
# one that a dependency brings is the same library, whoever asked for it
project github.com/owner/util util 1.0.0; echo 'from_dep : nat := 1.' > work/github.com/owner/util/u.soma
publish github.com/owner/util v1.0.0
project github.com/owner/usesutil usesutil 1.0.0 '"owner/util" = "1.0.0"'
printf 'Import util.u.\nfrom_b : nat := from_dep.\n' > work/github.com/owner/usesutil/b.soma
publish github.com/owner/usesutil v1.0.0
top '"owner/usesutil" = "1.0.0"'; mkdir util; echo 'mine : nat := 2.' > util/u.soma
printf 'Import usesutil.b.\nImport util.u.\nmine.\n' > main.soma
refused 'github.com/owner/util, which a dependency of this project needs, is named util, and this project has util/'
rm -rf util; echo 'mine : nat := 2.' > util.soma
refused 'is named util, and this project has util.soma'
rm util.soma; printf 'Import usesutil.b.\nfrom_b.\n' > main.soma
ok; says "= 1"
# a dependency's own folder of that name is not this project's: its files are under its name
project github.com/owner/hasutil hasutil 1.0.0 '"owner/usesutil" = "1.0.0"'
mkdir -p work/github.com/owner/hasutil/util; echo 'in_folder : nat := 5.' > work/github.com/owner/hasutil/util/w.soma
printf 'Import util.w.\nfive : nat := in_folder.\n' > work/github.com/owner/hasutil/h.soma
publish github.com/owner/hasutil v1.0.0
top '"owner/hasutil" = "1.0.0"'; printf 'Import hasutil.h.\nfive.\n' > main.soma
ok; says "= 5"

# * A checkout on disk, for a project being edited; it wins over a version
mkdir -p "$TMP/wip"
printf '[project]\nname = "wip"\nversion = "0.3.0"\n' > "$TMP/wip/soma.toml"
echo 'w : nat := 3.' > "$TMP/wip/w.soma"
top '"owner/wip" = { path = "../wip" }'
printf 'Import wip.w.\nw.\n' > main.soma
ok; says "= 3"
says 'version = "0.3.0"' soma.lock
if grep -q commit soma.lock; then cat soma.lock; exit 1; fi
[ ! -e "$TMP/wip/.soma-cache" ]
# a change in the checkout is picked up, as one in the project's files
echo 'w : nat := 4.' > "$TMP/wip/w.soma"
ok; says "= 4"
# a project fetched by others cannot name a folder of its author's
project github.com/owner/localdep localdep 1.0.0 '"owner/wip" = { path = "../wip" }'
mkdir -p work/github.com/owner/wip; printf '[project]\nname = "wip"\nversion = "0.3.0"\n' > work/github.com/owner/wip/soma.toml
printf '[project]\nname = "localdep"\nversion = "1.0.0"\n[dependencies]\n"owner/wip" = { path = "." }\n' > work/github.com/owner/localdep/soma.toml
publish github.com/owner/localdep v1.0.0
top '"owner/localdep" = "1.0.0"'; echo '1.' > main.soma
refused 'is a checkout on disk, which a project fetched by others cannot have'

# * A dependency has its folder's rules and proofs, not the importer's
project github.com/owner/ruled ruled 1.0.0
mkdir -p work/github.com/owner/ruled/lists
echo 'rule : nat := 7.' > work/github.com/owner/ruled/ruled.lang
echo 'in_rule : nat := 8.' > work/github.com/owner/ruled/lists/lists.lang
printf 'uses : nat := rule + in_rule.\n' > work/github.com/owner/ruled/lists/f.soma
printf 'Theorem uses_is : uses = 15.\nProof. reflexivity. Qed.\n' > work/github.com/owner/ruled/lists/f.proof
publish github.com/owner/ruled v1.0.0
top '"owner/ruled" = "1.0.0"'
printf 'Import ruled.lists.f.\nuses.\nCheck uses_is.\n' > main.soma
ok; says "= 15"; says "uses_is"
printf 'Import ruled.lists.f.\nCheck rule.\n' > main.soma
refused 'rule'
# a proof of a dependency that does not hold stops the build
project github.com/owner/ruled ruled 1.0.1
printf 'Theorem uses_is : uses = 16.\nProof. reflexivity. Qed.\n' > work/github.com/owner/ruled/lists/f.proof
publish github.com/owner/ruled v1.0.1
top '"owner/ruled" = "1.0.1"'
printf 'Import ruled.lists.f.\n1.\n' > main.soma
refused 'Cannot import ruled.lists.f: ruled/lists/f.soma does not compile'

# * A dependency brings its Rocq library along
project github.com/owner/withrocq withrocq 1.0.0
mkdir -p work/github.com/owner/withrocq/vendor/mylib/theories
printf -- '-Q theories mylib\ntheories/base.v\n' > work/github.com/owner/withrocq/vendor/mylib/_RocqProject
echo 'Definition base := 40.' > work/github.com/owner/withrocq/vendor/mylib/theories/base.v
cat > work/github.com/owner/withrocq/r.soma <<'EOT'
Rocq Library "mylib" in "vendor/mylib".
From mylib Require Import base.
fortytwo : nat := base + 2.
EOT
publish github.com/owner/withrocq v1.0.0
top '"owner/withrocq" = "1.0.0"'
printf 'Import withrocq.r.\nfortytwo.\n' > main.soma
ok; says "= 42"

# * soma explore reviews what a dependency brings; soma extract takes it along
project github.com/owner/hatch hatch 1.0.0
cat > work/github.com/owner/hatch/h.soma <<'EOT'
Definition unchecked : Any := 1.
greeting : string := "hello".
EOT
publish github.com/owner/hatch v1.0.0
top '"owner/hatch" = "1.0.0"'
printf 'Import hatch.h.\nFrom Stdlib Require Import Strings.String.\nmain : string := greeting.\n' > main.soma
soma explore main.soma > out.log 2>&1 || true
says 'unchecked'
if command -v opam > /dev/null; then
  soma extract main.soma -o ext > out.log 2>&1 || { cat out.log; exit 1; }
  says 'hello' ext/prog.ml
fi

# * A dependency is checked, not run: what writes where its argument says is
# refused while it compiles as a dependency, and runs when it is built on its own
OUT="$TMP/written"; mkdir -p "$OUT"
writes_nothing() { if [ -n "$(ls -A "$OUT")" ]; then echo "written:"; ls "$OUT"; exit 1; fi; }
# refused_write NAME COMMAND FIRST_LINE MESSAGE: a file of a dependency that runs it
refused_write() {
  project github.com/owner/"$1" "$1" 1.0.0
  printf 'From Corelib Require Extraction.\nDefinition d := 1.\n%s\n' "$2" > "$TMP/work/github.com/owner/$1/f.soma"
  publish github.com/owner/"$1" v1.0.0
  top "\"owner/$1\" = \"1.0.0\""
  printf 'Import %s.f.\n1.\n' "$1" > main.soma
  refused "$1.f:3: $3"
  says 'A dependency is checked, not run.'
  says 'works when that project is built on its own.'
  says "Cannot import $1.f"
  writes_nothing
  [ -z "$(ls "$XDG_CACHE_HOME"/soma/src/github.com/owner/"$1"@1.0.0-*/ | grep -v -e soma.toml -e f.soma)" ]
  # Explicit output targets on their own must stay inside their project.
  if [ "$1" = w_extraction ]; then
    printf 'From Corelib Require Extraction.\nDefinition d := 1.\nExtraction "e.ml" d.\n' > "$TMP/work/github.com/owner/$1/f.soma"
  fi
  if [ "$1" = w_redirect ] || [ "$1" = w_time ]; then
    printf 'Definition d := 1.\nTime Redirect "r" Check d.\n' > "$TMP/work/github.com/owner/$1/f.soma"
  fi
  # the same file, built on its own, runs it
  (cd "$TMP/work/github.com/owner/$1" && soma build f.soma > own.log 2>&1) || { cat "$TMP/work/github.com/owner/$1/own.log"; exit 1; }
  if [ "$1" = w_extraction ]; then
    [ -s "$TMP/work/github.com/owner/$1/e.ml" ]
  elif [ "$1" = w_redirect ] || [ "$1" = w_time ]; then
    [ -s "$TMP/work/github.com/owner/$1/r.out" ]
  else
    [ -n "$(ls -A "$OUT")" ] || { echo "$2 wrote nothing on its own"; exit 1; }
  fi
  rm -rf "$OUT"; mkdir -p "$OUT"
}
refused_write w_redirect "Redirect \"$OUT/r\" Check d." 'Redirect writes a file'
refused_write w_time "Time Redirect \"$OUT/r\" Check d." 'Redirect writes a file'
refused_write w_profile "Profile \"$OUT/p\" Check d." 'Profile writes a file'
refused_write w_universes "Print Universes \"$OUT/u.dot\"." 'Print Universes writes a file'
refused_write w_extraction "Extraction \"$OUT/e.ml\" d." 'Extraction writes a file'
# where they write by default, or to where it is set: the folder they run in
writes_here() { # NAME COMMANDS MESSAGE
  project github.com/owner/"$1" "$1" 1.0.0
  printf 'From Corelib Require Extraction.\nDefinition d := 1.\n%s\n' "$2" > "$TMP/work/github.com/owner/$1/f.soma"
  publish github.com/owner/"$1" v1.0.0
  top "\"owner/$1\" = \"1.0.0\""
  printf 'Import %s.f.\n1.\n' "$1" > main.soma
  refused "$1.f:3: $3"
  [ -z "$(find . -name '*.ml' -o -name '*.mli')" ]
  (cd "$TMP/work/github.com/owner/$1" && soma build f.soma > own.log 2>&1) || { cat "$TMP/work/github.com/owner/$1/own.log"; exit 1; }
}
writes_here w_separate 'Separate Extraction d.' 'Separate Extraction writes a file'
writes_here w_library 'Extraction Library Datatypes.' 'Extraction Library writes a file'
writes_here w_reclibrary 'Recursive Extraction Library Datatypes.' 'Recursive Extraction Library writes a file'
writes_here w_outdir "Set Extraction Output Directory \"$OUT\"." 'Set Extraction Output Directory says where files are written'
writes_here w_testcompile 'Extraction TestCompile d.' 'Extraction TestCompile writes a file'
writes_here w_native 'Set NativeCompute Profile Filename "p".' 'Set NativeCompute Profile Filename says where files are written'
rm -rf "$OUT"; mkdir -p "$OUT"
# a checkout on disk is compiled by someone else's Import too
mkdir -p "$TMP/wip2"
printf '[project]\nname = "wip2"\nversion = "0.1.0"\n' > "$TMP/wip2/soma.toml"
printf 'Definition d := 1.\nRedirect "%s/r" Check d.\n' "$OUT" > "$TMP/wip2/f.soma"
top '"owner/wip2" = { path = "../wip2" }'
printf 'Import wip2.f.\n1.\n' > main.soma
refused 'wip2.f:2: Redirect writes a file'; writes_nothing
# its .proof, what it imports of its own, a file it Loads, its Rocq library
project github.com/owner/w_proof w_proof 1.0.0
echo 'Definition d := 1.' > work/github.com/owner/w_proof/f.soma
printf 'Redirect "%s/r" Check d.\n' "$OUT" > work/github.com/owner/w_proof/f.proof
publish github.com/owner/w_proof v1.0.0
top '"owner/w_proof" = "1.0.0"'; printf 'Import w_proof.f.\n1.\n' > main.soma
refused 'w_proof.f.proof:1: Redirect writes a file'; writes_nothing
project github.com/owner/w_own w_own 1.0.0
printf 'Redirect "%s/r" Check 1.\n' "$OUT" > work/github.com/owner/w_own/inner.soma
echo 'Import inner.' > work/github.com/owner/w_own/f.soma
publish github.com/owner/w_own v1.0.0
top '"owner/w_own" = "1.0.0"'; printf 'Import w_own.f.\n1.\n' > main.soma
refused 'w_own.inner:1: Redirect writes a file'; writes_nothing
project github.com/owner/w_load w_load 1.0.0
printf 'Redirect "%s/r" Check 1.\n' "$OUT" > work/github.com/owner/w_load/loaded.soma
printf 'Load "%s/work/github.com/owner/w_load/loaded".\n' "$TMP" > work/github.com/owner/w_load/f.soma
publish github.com/owner/w_load v1.0.0
top '"owner/w_load" = "1.0.0"'
printf 'Import w_load.f.\n1.\n' > main.soma
refused 'Redirect writes a file'; writes_nothing
project github.com/owner/w_rocq w_rocq 1.0.0
mkdir -p work/github.com/owner/w_rocq/vendor/lib/theories
printf -- '-Q theories wlib\ntheories/base.v\n' > work/github.com/owner/w_rocq/vendor/lib/_RocqProject
printf 'Definition base := 1.\nRedirect "%s/r" Check base.\n' "$OUT" > work/github.com/owner/w_rocq/vendor/lib/theories/base.v
printf 'Rocq Library "wlib" in "vendor/lib".\n' > work/github.com/owner/w_rocq/f.soma
publish github.com/owner/w_rocq v1.0.0
top '"owner/w_rocq" = "1.0.0"'; printf 'Import w_rocq.f.\n1.\n' > main.soma
refused 'wlib.base:2: Redirect writes a file'; writes_nothing
# what writes nothing stays: printing, an output name not given, and Extract
project github.com/owner/w_fine w_fine 1.0.0
cat > work/github.com/owner/w_fine/f.soma <<'EOT'
From Corelib Require Extraction.
Definition d := 1.
Extraction d.
Recursive Extraction d.
Extraction Inline d.
Print Universes.
Unset Extraction Output Directory.
Time Check d.
EOT
publish github.com/owner/w_fine v1.0.0
top '"owner/w_fine" = "1.0.0"'; printf 'Import w_fine.f.\nd.\n' > main.soma
ok; says "= 1"
# this project's own files, imported or not, run them: only its dependencies do not
top
printf 'Redirect "own" Check 1.\n' > own.soma
printf 'Import own.\nRedirect "main" Check 2.\n1.\n' > main.soma
ok; [ -s own.out ] && [ -s main.out ]

# * Explicit Extraction targets stay in the project being built.
rm -rf "$OUT"; mkdir -p "$OUT"
top
mkdir sub
for target in "$OUT/absolute.ml" '../written/escape.ml' 'sub/../../written/escape.ml'; do
  printf 'From Corelib Require Extraction.\nDefinition d := 1.\nExtraction "%s" d.\n' "$target" > main.soma
  if soma build main.soma > out.log 2>&1; then
    echo "accepted Extraction target: $target"; exit 1
  fi
  says 'Extraction target'
  says "$target"
  writes_nothing
done
# Even from a subfolder, the relative target is rooted at the project.
printf 'From Corelib Require Extraction.\nDefinition d := 1.\nExtraction "sub/result.ml" d.\n' > sub/extract.soma
ok sub/extract.soma
[ -s sub/result.ml ] && [ -s sub/result.mli ]

# * Explicit Redirect targets also stay in the project being built.
for target in "$OUT/absolute" '../written/escape' 'sub/../../written/escape'; do
  printf 'Redirect "%s" Check 1.\n' "$target" > main.soma
  if soma build main.soma > out.log 2>&1; then
    echo "accepted Redirect target: $target"; exit 1
  fi
  says 'Redirect target'
  says "$target"
  writes_nothing
done
# Check the actual .out file and existing ancestors for symlink escapes.
ln -s "$OUT" sub/outside
ln -s "$OUT/symlink.out" sub/symlink.out
for target in sub/outside/escape sub/symlink; do
  printf 'Redirect "%s" Check 1.\n' "$target" > main.soma
  if soma build main.soma > out.log 2>&1; then
    echo "accepted Redirect target: $target"; exit 1
  fi
  says 'Redirect target'
  says "$target"
  writes_nothing
done
printf 'Time Redirect "sub/result" Check 1.\n' > sub/redirect.soma
ok sub/redirect.soma
[ -s sub/result.out ]
says 'nat' sub/result.out

# * A moved tag: soma.lock keeps its commit, and soma get says so
project github.com/owner/moves moves 1.0.0; echo 'm : nat := 1.' > work/github.com/owner/moves/m.soma
publish github.com/owner/moves v1.0.0
top '"owner/moves" = "1.0.0"'
printf 'Import moves.m.\nm.\n' > main.soma
ok; says "= 1"
echo 'm : nat := 2.' > "$TMP/work/github.com/owner/moves/m.soma"
git -C "$TMP/work/github.com/owner/moves" add -A
git -C "$TMP/work/github.com/owner/moves" commit -q -m moved
git -C "$TMP/work/github.com/owner/moves" tag -f v1.0.0 > /dev/null
git -C "$TMP/work/github.com/owner/moves" push -q -f origin HEAD refs/tags/v1.0.0
ok; says "= 1"
# with the source gone too, soma.lock is what is built
rm -rf "$XDG_CACHE_HOME"/soma/src/github.com/owner/moves@* .soma-cache
ok; says "= 1"
soma get > out.log 2>&1 || { cat out.log; exit 1; }
says 'its tag has moved, from'
ok; says "= 2"

# the tag rewritten, so that the commit is no ancestor of it
project github.com/owner/rewrites rewrites 1.0.0; echo 'm : nat := 1.' > work/github.com/owner/rewrites/m.soma
publish github.com/owner/rewrites v1.0.0
W="$TMP/work/github.com/owner/rewrites"; R="$TMP/remote/github.com/owner/rewrites.git"
git -C "$W" branch keep
echo x > "$W/x"; git -C "$W" checkout -q keep; git -C "$W" add -A; git -C "$W" commit -q -m later; git -C "$W" push -q origin keep
git -C "$W" checkout -q -; git -C "$W" reset -q --hard v1.0.0
top '"owner/rewrites" = "1.0.0"'
printf 'Import rewrites.m.\nm.\n' > main.soma
ok; says "= 1"
LOCK="$(cat soma.lock)"
echo 'm : nat := 2.' > "$W/m.soma"; git -C "$W" add -A; git -C "$W" commit -q --amend -m rewritten
git -C "$W" tag -f v1.0.0 > /dev/null; git -C "$W" push -q -f origin HEAD refs/tags/v1.0.0
gone() { rm -rf "$XDG_CACHE_HOME"/soma/src/github.com/owner/rewrites@* .soma-cache; }
# only behind a branch's tip, from a host that gives commits by id
gone; ok; says "= 1"
# and from one that gives only what it advertises: the tag does not have it
gone; GIT_CONFIG_COUNT=2 GIT_CONFIG_KEY_1=protocol.version GIT_CONFIG_VALUE_1=0 ok; says "= 1"
[ "$LOCK" = "$(cat soma.lock)" ]
# gone from the host: an error that says so, and not the tag's other program
git -C "$R" branch -q -D keep; git -C "$R" reflog expire --expire=now --all; git -C "$R" gc -q --prune=now
gone; refused 'is no longer on https://github.com/owner/rewrites.git'
says 'soma get writes it'
[ "$LOCK" = "$(cat soma.lock)" ]
soma get > out.log 2>&1 || { cat out.log; exit 1; }
ok; says "= 2"

# * soma get writes one line, and soma.lock
top
echo '1.' > main.soma
soma get owner/c@1.0.0 > out.log 2>&1 || { cat out.log; exit 1; }
says '"owner/c" = "1.0.0"' soma.toml
says 'version = "1.0.0"' soma.lock
# replaces it
soma get owner/c@1.2.0 > out.log 2>&1 || { cat out.log; exit 1; }
says '"owner/c" = "1.2.0"' soma.toml
[ "$(grep -c owner/c soma.toml)" = 1 ]
# the greatest tag of the path's major, added to the table
soma get owner/ann > out.log 2>&1 || { cat out.log; exit 1; }
says '"owner/ann" = "1.0.0"' soma.toml
# two majors of a project are two paths, of one name: not yet at once
if soma get owner/ann/v2 > out.log 2>&1; then echo "took two projects of one name"; exit 1; fi
says 'is named ann, and so is'
says '"owner/ann" = "1.0.0"' soma.toml
sed -i.bak '/owner\/ann/d' soma.toml
soma get owner/ann/v2 > out.log 2>&1 || { cat out.log; exit 1; }
says '"owner/ann/v2" = "2.0.0"' soma.toml
sed -i.bak '/owner\/ann\/v2/d' soma.toml
# what does not resolve leaves soma.toml as it was
cp soma.toml before.toml
if soma get owner/c@1.9.9 > out.log 2>&1; then echo "took a tag that is not there"; exit 1; fi
says 'no tag v1.9.9'
cmp soma.toml before.toml
if soma get owner/c@2.0.0 > out.log 2>&1; then echo "took major 2 at no /v2"; exit 1; fi
says 'Major 2 and above is "owner/c/v2" = "2.0.0"'
cmp soma.toml before.toml
cd "$TMP"; mkdir -p none; cd none
if soma get owner/c@1.0.0 > out.log 2>&1; then echo "wrote into no soma.toml"; exit 1; fi
says 'No soma.toml in'
