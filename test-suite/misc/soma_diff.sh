#!/usr/bin/env bash

# soma diff OLD NEW (vernac/somaDiff.ml): two versions of a project, each a tag
# or a folder, compared by what the kernel checked of them.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
TMP="$(pwd -P)"
export XDG_CACHE_HOME="$TMP/cache"
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0="url.file://$TMP/remote/.insteadOf" GIT_CONFIG_VALUE_0=https://
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t

# two versions of a project of that name, in old/ and new/
fresh() {
  rm -rf old new; mkdir old new
  printf '[project]\nname = "lib"\nversion = "1.0.0"\n' > old/soma.toml
  printf '[project]\nname = "lib"\nversion = "1.1.0"\n' > new/soma.toml
}
says() { grep -qF -- "$1" out.log || { echo "expected: $1"; cat out.log; exit 1; }; }
not_says() { if grep -qF -- "$1" out.log; then echo "did not expect: $1"; cat out.log; exit 1; fi; }
# under SECTION, the line LINE
under() {
  awk -v s="$1" -v l="  $2" 'index($0, s) == 1 { on = 1; next } /^$/ { on = 0 } on && $0 == l { f = 1 } END { exit !f }' out.log \
    || { echo "expected, under $1: $2"; cat out.log; exit 1; }
}
diff_() { soma diff old new > out.log 2>&1 || { cat out.log; exit 1; }; }
diff_fails() {
  if soma diff old new > out.log 2>&1; then
    echo 'an incomplete comparison reported success'; cat out.log; exit 1
  fi
  says 'The comparison is incomplete'
}

MORE='The same, and resting on more'
EDITED='Edited:'
BENEATH='Changed by what they use:'
LESS='The same, and resting on less:'
PROOF='Another proof, or one beneath it'

# * What is not in the kernel's terms is no change
fresh
echo 'double (n : nat) : nat := n + n.' > old/a.soma
printf '(* a comment *)\n\n\ndouble (m : nat) : nat :=\n   m + m.\n' > new/a.soma
diff_; says '1 unchanged.'
says 'old -> new'
not_says "$EDITED"

# * Edited, and what is above it apart from it
fresh
for v in old new; do
  printf 'Import a.\nquad (n : nat) : nat := double (double n).\n' > $v/b.soma
  printf 'Import b.\noct (n : nat) : nat := quad (quad n).\n' > $v/c.soma
  echo 'same : nat := 1.' > $v/s.soma
done
echo 'double (n : nat) : nat := n + n.' > old/a.soma
echo 'double (n : nat) : nat := 2 * n.' > new/a.soma
diff_
under "$EDITED" a.double
under "$BENEATH" b.quad
under "$BENEATH" c.oct
says '1 unchanged.'

# * Another proof; and what uses it, whose proof is beneath
fresh
for v in old new; do
  echo 'zero : nat := 0.' > $v/p.soma
  printf 'Import p.\nkeep : nat := 1.\n' > $v/q.soma
  printf 'Theorem u : 1 = 1.\nProof. exact (t 1). Qed.\n' > $v/q.exp
done
printf 'Theorem t : forall n : nat, n = n.\nProof. intro n. reflexivity. Qed.\n' > old/p.exp
printf 'Theorem t : forall n : nat, n = n.\nProof. intro n. destruct n; reflexivity. Qed.\n' > new/p.exp
diff_
under "$PROOF" p.t
under "$PROOF" q.u
not_says "$EDITED"
not_says "$BENEATH"
not_says "$MORE"

# * The same statement, resting on more, and on less the other way
fresh
for v in old new; do
  echo 'zero : nat := 0.' > $v/p.soma
  printf 'Import p.\nkeep : nat := 1.\n' > $v/q.soma
  printf 'Theorem u : 1 = 1.\nProof. exact t. Qed.\n' > $v/q.exp
done
printf 'Theorem t : 1 = 1.\nProof. reflexivity. Qed.\n' > old/p.exp
printf 'Axiom cheat : 1 = 1.\nTheorem t : 1 = 1.\nProof. exact cheat. Qed.\n' > new/p.exp
diff_
under "$MORE" 'p.t, now assumes p.cheat'
under "$MORE" 'q.u, now assumes p.cheat'
under 'Added:' p.cheat
not_says "$EDITED"
soma diff new old > out.log 2>&1
under "$LESS" 'p.t, no longer assumes p.cheat'
under 'Removed:' p.cheat

# a gradual elaboration is what it is
fresh
echo 'g (x : nat) : nat := x.' > old/g.soma
echo 'g (x : Any) : nat := x.' > new/g.soma
diff_
grep -q 'g.g, now assumes .*Gradual' out.log || { cat out.log; exit 1; }

# * Added, removed, moved or renamed
fresh
printf 'keep : nat := 1.\nold_only : nat := 2.\nold_name : nat := 3.\n' > old/a.soma
printf 'keep : nat := 1.\nnew_only : nat := 4.\n' > new/a.soma
printf 'new_name : nat := 3.\n' > new/moved.soma
diff_
under 'Added:' a.new_only
under 'Removed:' a.old_only
under 'Moved or renamed:' 'a.old_name -> moved.new_name'

# * A file that does not compile is said, and the others are compared
fresh
for v in old new; do echo 'fine : nat := 1.' > $v/fine.soma; done
echo 'broken : nat := 1.' > old/broken.soma
echo 'broken : nat := true.' > new/broken.soma
echo 'same_edit : nat := 1.' > old/e.soma; echo 'same_edit : nat := 2.' > new/e.soma
diff_fails
says 'Not compared, as it does not compile in new:'
says 'broken'
under "$EDITED" e.same_edit
says '1 unchanged.'

# * It is checked, as a dependency, and not run; and nothing is written to it
fresh
OUT="$TMP/written"; mkdir -p "$OUT"
echo 'x : nat := 1.' > old/w.soma
printf 'x : nat := 1.\nRedirect "%s/r" Check x.\n' "$OUT" > new/w.soma
diff_fails
says 'Not compared, as it does not compile in new:'
says 'Redirect writes a file'
not_says 'Removed:'
[ -z "$(ls -A "$OUT")" ]
[ "$(ls -A old | sort | tr '\n' ' ')" = 'soma.toml w.soma ' ]
[ ! -e soma.lock ] && [ ! -e .soma-cache ]

# * What is no part of it: a project inside it, a folder that is no name
fresh
for v in old new; do
  echo 'x : nat := 1.' > $v/x.soma
  mkdir -p $v/inner $v/not-a-name
  printf '[project]\nname = "inner"\nversion = "1.0.0"\n' > $v/inner/soma.toml
  echo 'bad : nat := true.' > $v/inner/i.soma
  echo 'bad : nat := true.' > $v/not-a-name/n.soma
done
diff_; says '1 unchanged.'; not_says 'does not compile'

# * What a version depends on, through what it uses
fresh; rm -rf c1 c2; mkdir c1 c2
printf '[project]\nname = "c"\nversion = "1.0.0"\n' > c1/soma.toml; echo 'v : nat := 1.' > c1/c.soma
printf '[project]\nname = "c"\nversion = "1.1.0"\n' > c2/soma.toml; echo 'v : nat := 2.' > c2/c.soma
printf '\n[dependencies]\n"o/c" = { path = "../c1" }\n' >> old/soma.toml
printf '\n[dependencies]\n"o/c" = { path = "../c2" }\n' >> new/soma.toml
for v in old new; do printf 'Import c.c.\nw : nat := v.\n' > $v/u.soma; done
diff_
under "$BENEATH" u.w
not_says 'c.c.v'

# * Tags
publish() {
  local work="$TMP/work/$1" bare="$TMP/remote/$1.git"
  if [ ! -d "$bare" ]; then
    mkdir -p "$bare"; git -C "$bare" init -q --bare
    git -C "$work" init -q; git -C "$work" remote add origin "$bare"
  fi
  git -C "$work" add -A; git -C "$work" commit -q -m "$2" --allow-empty
  git -C "$work" tag "$2"; git -C "$work" push -q origin HEAD "refs/tags/$2"
}
W="$TMP/work/github.com/owner/lib"; mkdir -p "$W"
printf '[project]\nname = "lib"\nversion = "1.0.0"\n' > "$W/soma.toml"; echo 'a : nat := 1.' > "$W/a.soma"
publish github.com/owner/lib v1.0.0
printf '[project]\nname = "lib"\nversion = "1.1.0"\n' > "$W/soma.toml"; echo 'a : nat := 2.' > "$W/a.soma"
publish github.com/owner/lib v1.1.0
printf '[project]\nname = "lib"\nversion = "2.0.0"\n' > "$W/soma.toml"; echo 'a : nat := 3.' > "$W/a.soma"
publish github.com/owner/lib v2.0.0
soma diff owner/lib@1.0.0 owner/lib@1.1.0 > out.log 2>&1 || { cat out.log; exit 1; }
says 'owner/lib 1.0.0 -> owner/lib 1.1.0'
under "$EDITED" a.a
# across a major, a path of its own; and a tag against a folder
soma diff owner/lib@v1.1.0 owner/lib/v2@2.0.0 > out.log 2>&1 || { cat out.log; exit 1; }
under "$EDITED" a.a
fresh; echo 'a : nat := 2.' > old/a.soma
soma diff owner/lib@1.1.0 old > out.log 2>&1 || { cat out.log; exit 1; }
says '1 unchanged.'

# * What it is asked
refuses() { if soma diff "$@" > out.log 2>&1; then echo "took: $*"; cat out.log; exit 1; fi; }
refuses old; says 'soma diff compares two versions'
refuses old nowhere; says 'nowhere is no version of a project'
refuses owner/lib@1.9.9 old; says 'no tag v1.9.9'
refuses owner/lib@2.0.0 old; says 'Major 2 and above is'
