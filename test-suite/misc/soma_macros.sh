#!/usr/bin/env bash

# Soma macros (vernac/somaMacro.ml): [Macro] in .lang files only; the
# macros of FILE.lang are in scope in FILE.soma and FILE.proof; another
# .lang file's macros are in scope where it is loaded or imported, and
# nowhere else; the Macro library is not in scope in .soma files.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

fails() { # fails FILE MESSAGE: compiling FILE fails, with MESSAGE
  if rocq c -q "$1" > out.log 2>&1; then
    echo "$1 was accepted"; exit 1
  fi
  grep -q "$2" out.log || { cat out.log; exit 1; }
}

cat > prog.lang <<'EOT'
Macro swap args :=
  match args with
  | cons f (cons a (cons b nil)) => App f (cons b (cons a nil))
  | _ => MacroError "swap takes a function and two arguments"
  end.
Macro twice args :=
  match args with
  | cons f (cons x nil) => App f (cons (App f (cons x nil)) nil)
  | _ => MacroError "twice takes a function and an argument"
  end.
Macro loop args := App (Var "loop") nil.
EOT

# the macros of prog.lang, in prog.soma and prog.proof; a match is
# passed through a macro unchanged (Opaque)
cat > prog.soma <<'EOT'
Definition a : swap Nat.sub 1 5 = 4 := eq_refl.
Definition b : twice S 0 = 2 := eq_refl.
Definition c : swap Nat.sub 2 (match 5 with 0 => 0 | _ => 9 end) = 7 := eq_refl.
EOT
cat > prog.proof <<'EOT'
Theorem swap_sub : forall m n, swap Nat.sub m n = n - m.
Proof. reflexivity. Qed.
EOT
rocq c -q prog.soma
rm prog.proof

# a macro's error, at the use
echo 'Definition d := twice S.' >> prog.soma
fails prog.soma "twice takes a function and an argument"
# a macro that expands to itself stops
sed -i.bak '$d' prog.soma && echo 'Definition d := loop.' >> prog.soma
fails prog.soma "The macro loop was expanded 1000 times"

# Macro, outside a .lang file
echo 'Macro m args := Hole.' > bad.soma
fails bad.soma "Macro can only be used in a .lang file"
# the Macro library, outside a .lang file
echo 'Check App.' > nolib.soma
fails nolib.soma "The reference App was not found"

# another .lang file: its macros where it is loaded, and not elsewhere
cat > strings.lang <<'EOT'
Macro repeat args :=
  match args with
  | cons (Str s) (cons (Num n) nil) =>
    Str ((fix go k := match k with 0 => "" | Succ m => append s (go m) end) n)
  | _ => MacroError "repeat takes a string literal and a number literal"
  end.
EOT
cat > user.soma <<'EOT'
Load "strings.lang".
Definition e : repeat "ab" 3 = "ababab" := eq_refl.
EOT
rocq c -q user.soma
echo 'Definition f := swap Nat.sub 1 5.' >> user.soma
fails user.soma "The reference swap was not found"

# a .lang file compiled by itself: its macros where it is imported
rocq c -q strings.lang
cat > imported.soma <<'EOT'
Require Import strings.
Definition g : repeat "ab" 2 = "abab" := eq_refl.
EOT
rocq c -q -Q . "" imported.soma
cat > required.soma <<'EOT'
Require strings.
Definition h : repeat "ab" 2 = "abab" := eq_refl.
EOT
fails required.soma "The term"
