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

# an error in FILE.lang: located in FILE.lang, not an anomaly. A syntax
# error, and an error in a sentence that parses (each was "Anomaly ...
# stm.ml ... Assertion failed", with no location)
mkdir errs && cd errs
printf 'Macro m args := App (Var "f") nil |> x.\n' > syn.lang
echo 'Definition x := 1.' > syn.soma
fails syn.soma 'File "./syn.lang", line 1, characters 34-35'
grep -q "Anomaly" out.log && { cat out.log; exit 1; }
printf 'Inductive m := A.\nMacro m args := Var "x".\n' > clash.lang
echo 'Definition x := 1.' > clash.soma
fails clash.soma 'File "./clash.lang", line 2, characters 0-24'
grep -q "m already exists" out.log || { cat out.log; exit 1; }
cd ..

# let and match, in the code a macro is given and returns: a macro that
# returns a match makes structural recursion; a match with simple
# patterns is quoted as Match, any other is Opaque
mkdir letmatch && cd letmatch
cat > lm.lang <<'EOS'
Macro natcase args :=
  match args with
  | cons n (cons z (cons m (cons s nil))) =>
    Match n (cons (Num 0, z) (cons (App (Var "Succ") (cons m nil), s) nil))
  | _ => MacroError "natcase n zero m succ"
  end.
Macro let1 args :=
  match args with
  | cons (Var x) (cons v (cons b nil)) => LetIn x v b
  | _ => MacroError "let1 x v b"
  end.
Macro branches args :=
  match args with
  | cons (Match _ bs) nil => Num (List.length bs)
  | cons (Opaque _) nil => Num 99
  | _ => MacroError "branches takes a match"
  end.
Macro swap_bool args :=
  match args with
  | cons (Match s (cons (p1, b1) (cons (p2, b2) nil))) nil => Match s (cons (p1, b2) (cons (p2, b1) nil))
  | _ => MacroError "swap_bool takes a match with two branches"
  end.
Macro badpat args := Match (Num 1) (cons (Lam "x" Hole, Num 0) nil).
EOS
cat > lm.soma <<'EOS'
Recursive fact n := natcase n 1 m (n * fact m).
Definition a : fact 5 = 120 := eq_refl.
Definition b : let1 x 4 (x * x) = 16 := eq_refl.
Definition c : branches (match 3 with 0 => 1 | Succ k => k | _ => 0 end) = 3 := eq_refl.
Definition d : branches (match [1] with [] => 0 | _ :: _ => 1 end) = 99 := eq_refl.
Definition e : swap_bool (match true with true => 1 | false => 2 end) = 2 := eq_refl.
Definition f : branches (match (1, 2) with (x, y) => x end) = 99 := eq_refl.
Definition g : branches (match cons 1 nil with cons x _ => x | nil => 0 end) = 2 := eq_refl.
EOS
rocq c -q lm.soma
echo 'Definition h := badpat.' >> lm.soma
fails lm.soma "returned a pattern that is not a name"
cd ..
