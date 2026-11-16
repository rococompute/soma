#!/usr/bin/env bash

# soma search QUERY [FILE] (vernac/somaSearch.ml): definitions and theorems by
# name, or by the shape of their types, with where each is and what it assumes.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
TMP="$(pwd -P)"
export XDG_CACHE_HOME="$TMP/cache"

says() { grep -qF -- "$1" out.log || { echo "expected: $1"; cat out.log; exit 1; }; }
not_says() { if grep -qF -- "$1" out.log; then echo "did not expect: $1"; cat out.log; exit 1; fi; }
search() { soma search "$@" > out.log 2>&1 || { cat out.log; exit 1; }; }
# the first line of the results is
first() { [ "$(head -1 out.log)" = "$1" ] || { echo "first should be: $1"; cat out.log; exit 1; }; }

mkdir lib app
printf '[project]\nname = "lib"\nversion = "1.0.0"\n' > lib/soma.toml
cat > lib/rates.soma <<'EOT'
(* a comment, so that what follows is on line 2 *)
discount (percent price : nat) : nat := price * percent / 100.
discounted (percent price : nat) : nat := price - discount percent price.
EOT
cat > lib/rates.exp <<'EOT'
Axiom discount_small : forall percent price, discount percent price <= price.

Theorem discount_le : forall percent price, percent <= 100 -> discount percent price <= price.
Proof. intros percent price _. apply discount_small. Qed.

Theorem discounted_le : forall percent price, discounted percent price <= price.
Proof. intros percent price. unfold discounted. lia. Qed.
EOT
printf '[project]\nname = "app"\nversion = "0.1.0"\n\n[dependencies]\n"o/lib" = { path = "../lib" }\n' > app/soma.toml
cat > app/main.soma <<'EOT'
Import lib.rates.
Fixpoint total (prices : list nat) : nat :=
  match prices with [] => 0 | p :: r => p + total r end.
half (n : nat) : nat := n / 2.
EOT
printf 'Theorem half_le : forall n, half n <= n.\nProof. intro n. unfold half. apply Nat.Div0.div_le_upper_bound. lia. Qed.\n' > app/main.exp
cd app

# * A name: itself first, wherever it is, with its file and line
search discount
case "$(head -1 out.log)" in
  */lib/rates.soma:2:\ lib.rates.discount\ :\ nat\ -\>\ nat\ -\>\ nat) ;;
  *) echo "a name should come first:"; cat out.log; exit 1 ;;
esac
# part of a name, and what mentions it
says 'lib.rates.discounted :'
says 'lib.rates.discount_le :'
# what it assumes: an axiom is told from a theorem
grep -A1 'lib.rates.discount_small :' out.log | grep -qF 'is assumed, and not proved' || { cat out.log; exit 1; }
grep -A1 'lib.rates.discount_le :' out.log | grep -qF 'assumes lib.rates.discount_small' || { cat out.log; exit 1; }
if grep -A1 'lib.rates.discounted_le :' out.log | grep -q 'assumes'; then cat out.log; exit 1; fi
# this project's own files, by a path from here
search half
first 'main.soma:4: main.half : nat -> nat'
says 'main.exp:1: main.half_le :'
# a theorem by its own name, and only it
search discount_le
[ "$(grep -c ' : ' out.log)" = 1 ] || { cat out.log; exit 1; }
# a qualified name
search lib.rates.discount
says 'lib.rates.discount :'

# * A typo finds what is close, and says so; nothing is nothing
search discont
first 'Nothing of that name. Similar names:'
says 'lib.rates.discount :'
search zzzzzzzzzzzz
first 'Nothing found.'
# what is close is not shown beside what matches
search half
not_says 'Similar'

# * A type, without its parentheses: all of it, before its conclusion, before a part
search 'nat -> nat -> nat' --limit 0
says 'lib.rates.discount :'
search 'list nat -> nat'
first 'main.soma:2: main.total : list nat -> nat'
search '_ <= _' --limit 3
says 'main.half_le'
says '3 of'
# as Search takes it: a string, and two conditions
search '"total"'
first 'main.soma:2: main.total : list nat -> nat'
search 'discount "le"'
says 'lib.rates.discount_le'
not_says 'lib.rates.discount_small :'

# * What rests on nothing
search '_ <= _' --no-assumptions --limit 0
says 'lib.rates.discounted_le'
not_says 'lib.rates.discount_le'
not_says 'lib.rates.discount_small :'
says 'main.half_le'

# * For an agent: a JSON object to a line, and nothing else on stdout
soma search discount_le --json > out.log 2>/dev/null
says '"name":"lib.rates.discount_le"'
says '"match":"exact"'
says '"scope":"dependency"'
says '"line":3'
says '"assumes":["lib.rates.discount_small"]'
grep -q '"contract":"[0-9a-f]\{64\}"' out.log || { cat out.log; exit 1; }
soma search half --json > out.log 2>/dev/null
says '"scope":"project"'
says '"file":"main.soma"'
soma search zzzzzzzzzzzz --json > out.log 2>/dev/null
[ ! -s out.log ]

# * A file that does not compile is said, and the others searched
printf 'half (n : nat) : nat := true.\n' > broken.soma
search half
says 'Not searched, as it does not compile: broken'
says 'main.half'
rm broken.soma
# one that what is searched imports: the one left out, with it
printf 'b : nat := true.\n' > low.soma
printf 'Import low.\nc : nat := b.\n' > high.soma
search half
says 'Not searched, as it does not compile: high'
says 'Not searched, as it does not compile: low'
says 'main.half'
rm low.soma high.soma

# * What a file sees, with its notations; and what it does not
cat > nota.soma <<'EOT'
Notation "!!" := 7.
Definition seven : nat := 7.
Definition uses_it : seven = !! := eq_refl.
EOT
search seven nota.soma
says 'nota.seven'
says 'nota.uses_it'
# a query that means nothing says what to do
if soma search 'list nat ->' > out.log 2>&1; then cat out.log; exit 1; fi
says 'does not mean anything here'
says 'soma search QUERY FILE'
# a FILE that does not compile, or is not there
printf 'x : nat := true.\n' > bad.soma
if soma search x bad.soma > out.log 2>&1; then cat out.log; exit 1; fi
rm bad.soma
if soma search x nowhere.soma > out.log 2>&1; then cat out.log; exit 1; fi
says 'nowhere.soma does not exist'
if soma search > out.log 2>&1; then cat out.log; exit 1; fi
says 'soma search QUERY'

# * What it changes in a project: its cache, as a build does, and nothing else
ls -A | sort > "$TMP/before.txt"
cksum soma.toml soma.lock main.soma > "$TMP/before.sum"
search discount
ls -A | sort > "$TMP/after.txt"
cmp "$TMP/before.txt" "$TMP/after.txt"
cksum soma.toml soma.lock main.soma | cmp - "$TMP/before.sum"
[ -z "$(ls -A ../lib | grep -v -e soma.toml -e rates)" ]

# * With no project: Soma's own libraries
mkdir "$TMP/none"; cd "$TMP/none"
soma search 'nat -> nat -> nat' --limit 1 > out.log 2>&1 || { cat out.log; exit 1; }
says 'No soma.toml in'
says 'nat -> nat -> nat'
