#!/usr/bin/env bash

# A folder's rules, X/X.lang with its proofs in X/X.proof, apply to every
# Soma file under X/: they are compiled once into the project's
# .soma-cache and imported first (vernac/somaImport.ml, folder_rules).

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

mkdir -p outer/inner
cat > outer/outer.lang <<'EOT'
twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Macro first args := match args with cons x _ => x | nil => MacroError "first takes one" end.
EOT
cat > outer/outer.proof <<'EOT'
Theorem twice_twice : forall (f : nat -> nat) x, twice (twice f) x = f (f (f (f x))).
Proof.
  The rest follows.
Qed.
EOT
# the rules of outer/inner/ see those of outer/
cat > outer/inner/inner.lang <<'EOT'
quadruple (f : nat -> nat) : nat -> nat := twice (twice f).
EOT
cat > outer/inner/use.soma <<'EOT'
four := quadruple (fun n => n + 1) 0.
pick := first 7 8.
EOT
cat > outer/inner/use.proof <<'EOT'
Theorem four_is_4 : four = 4.
Proof.
  By twice_twice, we conclude that four = 4.
Qed.
EOT
cat > main.soma <<'EOT'
Import outer.inner.use.
four.
pick.
Fail first 1 2.
Fail twice (fun n => n) 0.
EOT

compiled() { grep -c '^Compiling' err.log || true; }

# the rules are compiled once each, and apply below their folder only
soma build -v main.soma > out.log 2> err.log
grep -q '= 4' out.log
grep -q '= 7' out.log
[ "$(compiled)" = 3 ]
grep -q '^Compiling outer/outer.lang' err.log
grep -q '^Compiling outer/inner/inner.lang' err.log
soma build main.soma > out.log 2> err.log
[ "$(compiled)" = 0 ]

# a change to the rules compiles what they apply to again
echo 'thrice {A : Type} (f : A -> A) (x : A) : A := f (f (f x)).' >> outer/outer.lang
soma build main.soma > out.log 2> err.log
[ "$(compiled)" = 3 ]

# a proof of the rules that does not hold fails what they apply to
sed -i.bak 's/f (f (f (f x)))/f (f (f x))/' outer/outer.proof
if soma build main.soma > out.log 2> err.log; then
  echo "a false proof of a folder's rules did not fail the build"; exit 1
fi
grep -q 'Cannot import outer.outer: outer/outer.lang does not compile' err.log
mv outer/outer.proof.bak outer/outer.proof

# built by itself, a file is its own project: the rules above it do not
# apply, and it says so; SOMA_PROJECT_ROOT makes them apply
if soma build outer/inner/use.soma > out.log 2> err.log; then
  echo "a file built by itself had the rules of the folders above it"; exit 1
fi
grep -q 'outer/outer.lang, the rules of the folder outer/ this file is under, does not apply to it' err.log
SOMA_PROJECT_ROOT=. soma build outer/inner/use.soma > out.log 2> err.log

# X/X.lang next to X/X.soma is that program's, as before, not the folder's
mkdir prog
printf 'Macro one args := Num 1.\n' > prog/prog.lang
printf 'x := one.\n' > prog/prog.soma
printf 'y := one.\n' > prog/other.soma
printf 'Import prog.prog.\nx.\n' > useprog.soma
soma build -v useprog.soma > out.log 2> err.log
grep -q '= 1' out.log
if soma build prog/other.soma > out.log 2> err.log; then
  echo "a program's .lang applied to the other files of its folder"; exit 1
fi

# the proofs of rules that do not exist
mkdir lone
printf 'Theorem t : 1 = 1.\nProof.\n  The rest follows.\nQed.\n' > lone/lone.proof
printf 'z := 1.\n' > lone/z.soma
printf 'Import lone.z.\n' > uselone.soma
if soma build uselone.soma > out.log 2> err.log; then
  echo "lone/lone.proof without lone/lone.lang did not fail"; exit 1
fi
grep -q 'lone/lone.proof has the proofs of the rules of its folder, lone/lone.lang, which does not exist.' err.log
