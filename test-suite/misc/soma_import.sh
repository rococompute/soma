#!/usr/bin/env bash

# In a Soma file, [Import X] of a file of the project (X.soma, X/Y.soma for
# X.Y) compiles it into the project's .soma-cache when it is not up to
# date, then loads it (vernac/somaImport.ml); a compiled file is used again
# while its stamp holds: its source unchanged, and what it imports the
# same as when it was compiled.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
# its own shared build store (topbin/soma.ml): one kept from an earlier run
# would skip the compiles this test counts
export SOMA_CACHE="$TMP/.soma-store"

mkdir models
cat > models/item.soma <<'EOT'
Record item := { name : string; count : nat }.
EOT
cat > stock.soma <<'EOT'
Import models.item.
total (xs : list item) : nat := fold_left (fun n x => n + count x) xs 0.
EOT
cat > stock.proof <<'EOT'
Theorem total_nil : total nil = 0.
Proof.
  Computing, we conclude that 0 = 0.
Qed.
EOT
cat > show.soma <<'EOT'
Import models.item.
show (x : item) : string := name x.
EOT
cat > main.soma <<'EOT'
Import models.item.
Import stock.
Import show.
Import Stdlib.Bool.Bool.
stock := [{| name := "a"; count := 2 |}, {| name := "b"; count := 3 |}].
total stock.
EOT

compiled() { grep -c '^Compiling' err.log || true; }

# everything is compiled once, models/item for both
soma build -v main.soma > out.log 2> err.log
grep -q '= 5' out.log
[ "$(compiled)" = 3 ]
grep -q '^Compiling models/item.soma (into .soma-cache)$' err.log
[ -f .soma-cache/models/item.vo ] && [ -f .soma-cache/stock.stamp ]
! grep -q 'soma-cache\|models$' out.log

# nothing changed: nothing is compiled
soma build main.soma > out.log 2> err.log
[ "$(compiled)" = 0 ]

# a changed file is compiled again, and what imports it is not, while it
# compiles to the same (a .vo has locations: here the change moves none)
echo '(* a comment *)' | cat - show.soma > s && mv s show.soma
echo '(* a comment *)' >> models/item.soma
soma build main.soma > out.log 2> err.log
[ "$(compiled)" = 2 ]
grep -q '^Compiling show.soma' err.log
grep -q '^Compiling models/item.soma' err.log

# when it compiles to something else, what imports it is compiled again
echo 'empty := {| name := ""; count := 0 |}.' >> models/item.soma
soma build main.soma > out.log 2> err.log
[ "$(compiled)" = 3 ]

# a change to a .proof is a change of its program, and a proof that does
# not hold fails the import
sed -i.bak 's/0 = 0/0 = 1/' stock.proof
if soma build main.soma > out.log 2> err.log; then
  echo "a false proof in an imported file did not fail the build"; exit 1
fi
grep -q 'Cannot import stock: stock.soma does not compile' err.log
mv stock.proof.bak stock.proof

# so does an error in what it imports
echo 'oops := undefined_thing.' >> models/item.soma
if soma build main.soma > out.log 2> err.log; then
  echo "an error in an imported file did not fail the build"; exit 1
fi
grep -q 'undefined_thing' err.log
grep -q 'Cannot import models.item: models/item.soma does not compile' err.log
sed -i.bak '/oops/d' models/item.soma

# soma run, from another folder, uses the project's cache: the failed
# compilations left it as it was, which the files are again
cd /
soma run "$TMP/main.soma" > "$TMP/out.log" 2> "$TMP/err.log"
cd "$TMP"
grep -q '= 5' out.log
[ "$(compiled)" = 0 ]

# a stamp holds the digests of the libraries from elsewhere (Stdlib, ...)
# that the file was compiled with: one that changed (an upgrade of Soma)
# compiles the file again, and so does a stamp of an older format
grep -q '^soma-stamp 3$' .soma-cache/show.stamp
grep -q '^library Corelib.Init.Prelude ' .soma-cache/show.stamp
sed -i.bak 's/^\(library Corelib.Init.Prelude\) .*/\1 0/' .soma-cache/show.stamp
soma build main.soma > out.log 2> err.log
[ "$(compiled)" = 1 ]
grep -q '^Compiling show.soma' err.log
sed -i.bak '1d' .soma-cache/show.stamp
soma build main.soma > out.log 2> err.log
[ "$(compiled)" = 1 ]

# a cycle is reported as such
printf 'Import b.\n' > a.soma
printf 'Import a.\n' > b.soma
if soma build a.soma > out.log 2> err.log; then
  echo "an import cycle did not fail the build"; exit 1
fi
grep -q 'Import cycle: a -> b -> a.' err.log

# a module in scope is imported as before; mixing one with a file is an error
cat > mods.soma <<'EOT'
Module M. Definition x := 1. End M.
Import M.
Import M stock.
EOT
if soma build mods.soma > out.log 2> err.log; then
  echo "importing a module and a file in one command did not fail"; exit 1
fi
grep -q 'Import modules in scope and libraries or files in separate commands.' err.log

# Another proof compiles the file and nothing that imports it. What else a
# file says does: a notation is no proof, and goes on through what imports it.
mkdir "$TMP/proofs"; cd "$TMP/proofs"
printf 'x1 : nat := 1.\nx2 : nat := 2.\nNotation "!!" := x1.\n' > a.soma
printf 'Theorem t : forall n : nat, n = n.\nProof. intro n. reflexivity. Qed.\n' > a.proof
printf 'Import a.\nview : nat := !!.\n' > b.soma
printf 'Import b.\nfinal : nat := view.\nfinal.\n' > main.soma
soma build -v main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q '= 1' out.log
printf 'Theorem t : forall n : nat, n = n.\nProof. intro n. destruct n; reflexivity. Qed.\n' > a.proof
soma build -v main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q 'Compiling a.soma' out.log
if grep -q 'Compiling b.soma' out.log; then echo "another proof compiled an importer"; cat out.log; exit 1; fi
sed -i.bak 's/:= x1\./:= x2./' a.soma
soma build -v main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q 'Compiling b.soma' out.log
grep -q '= 2' out.log
# a change that leaves the file in between compiled the same still reaches past
# it: Rocq would not load what imports it otherwise
mkdir "$TMP/chain"; cd "$TMP/chain"
printf 'x : nat := 1.\n' > a.soma
printf 'Import a.\ny : nat := 7.\n' > b.soma
printf 'Import b.\nz : nat := y.\n' > c.soma
printf 'Import c.\nz.\n' > main.soma
soma build -v main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q '= 7' out.log
printf 'x : nat := 1.\nspare : nat := 9.\n' > a.soma
soma build -v main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q 'Compiling b.soma' out.log
grep -q 'Compiling c.soma' out.log
grep -q '= 7' out.log
