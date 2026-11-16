#!/usr/bin/env bash

# Soma readers (vernac/somaMacro.ml): [Reader name text := body.] in a
# .ext file; [Read name "text".] and a first line [#lang name] run the
# forms the reader returns (Def, RecDef, Expr), and a ReadError, or an
# error in a form, is reported where it is in the text.

set -euo pipefail

export PATH=$BIN:$PATH
HERE="$(cd "$(dirname "$0")" && pwd)"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

fails() { # fails FILE MESSAGE: compiling FILE fails, with MESSAGE
  if rocq c -q "$1" > out.log 2>&1; then
    echo "$1 was accepted"; exit 1
  fi
  grep -qF "$2" out.log || { cat out.log; exit 1; }
}

# tiny: two := 2, dbl by structural recursion, dbl two; a "!" in the text
# is an error there, a "?" a definition of a name that is not one, a "%"
# a recursion that is not structural
cat > tiny.ext <<'EOT'
Fixpoint find (k : nat) (cs : list nat) (i : nat) : option nat :=
  match cs with nil => None | cons c r => if Nat.eqb c k then Some i else find k r (Succ i) end.

Reader tiny text :=
  match find 33 (chars text) 0, find 63 (chars text) 0, find 37 (chars text) 0 with
  | Some p, _, _ => cons (ReadError p "no ! here") nil
  | _, Some p, _ => cons (Def p "not-a-name" (Num 1)) nil
  | _, _, Some p => cons (RecDef p "loop" (cons "n" nil) (App (Var "loop") (cons (Var "n") nil))) nil
  | None, None, None =>
    cons (Def 0 "two" (Num 2))
    (cons (RecDef 0 "dbl" (cons "n" nil)
             (Match (Var "n") (cons (Num 0, Num 0)
                (cons (App (Var "Succ") (cons (Var "m") nil),
                       App (Var "Succ") (cons (App (Var "Succ") (cons (App (Var "dbl") (cons (Var "m") nil)) nil)) nil)) nil))))
    (cons (Expr 0 (App (Var "dbl") (cons (Var "two") nil))) nil))
  end.

Reader broken text := raise.
EOT

# Read: the forms run where it is, and what they define is in scope after
cp tiny.ext prog.ext
cat > prog.soma <<'EOT'
Read tiny "anything".
Definition four : dbl two = 4 := eq_refl.
EOT
rocq c -q prog.soma > /dev/null

# a ReadError, at its place in the string (its quotes written doubled)
cp tiny.ext quoted.ext
printf 'Read tiny "line one\nab ""q"" !".\n' > quoted.soma
fails quoted.soma 'File "./quoted.soma", line 2, characters 9-10'
grep -q "no ! here" out.log || { cat out.log; exit 1; }

# a name that is not one, and a recursion Rocq rejects, at their place
cp tiny.ext names.ext
printf 'Read tiny "\n  x ?".\n' > names.soma
fails names.soma 'File "./names.soma", line 2'
grep -q 'defined "not-a-name", which is not a name' out.log || { cat out.log; exit 1; }
cp tiny.ext rec.ext
printf 'Read tiny "\n\n %%".\n' > rec.soma
fails rec.soma 'File "./rec.soma", line 3'

# #lang: the rest of the file is the text
cp tiny.ext whole.ext
printf '#lang tiny\nanything at all, even ( * and "\n' > whole.soma
rocq c -q whole.soma > /dev/null
cp tiny.ext wholeerr.ext
printf '#lang tiny\nfirst\n  second ! x\n' > wholeerr.soma
fails wholeerr.soma 'File "./wholeerr.soma", line 3, characters 9-12'

# a #lang file imported by another file of its project
mkdir proj
cp tiny.ext proj/tinydefs.ext
printf '#lang tiny\nanything\n' > proj/tinydefs.soma
printf 'Import tinydefs.\nDefinition four : dbl two = 4 := eq_refl.\n' > proj/main.soma
(cd proj && soma compile main.soma > out.log 2>&1) || { cat proj/out.log; exit 1; }

# errors: an unknown reader, something that is not one, Reader outside a
# .ext file, a reader that fails
printf '#lang nosuch\nx\n' > unknown.soma
fails unknown.soma "The reader nosuch was not found"
echo 'Read Nat.add "x".' > notreader.soma
fails notreader.soma "Nat.add is not a reader"
echo 'Reader r t := nil.' > outside.soma
fails outside.soma "Reader can only be used in a .ext file"
cp tiny.ext fail.ext
echo 'Read broken "x".' > fail.soma
fails fail.soma "The reader broken did not return forms"

# the example: examples/example_files/lisp, a #lang lisp program, its
# values and its proofs
EXAMPLE="$(cd "$HERE/../../examples/example_files/lisp" 2>/dev/null && pwd || true)"
if [ -n "$EXAMPLE" ] && [ -f "$EXAMPLE/lisp.soma" ]; then
  mkdir example && cp "$EXAMPLE"/lisp.* example/
  (cd example && soma compile -v lisp.soma > out.log 2>&1) || { cat example/out.log; exit 1; }
  for v in '= 144' '= 120' '= 35' '= "less"' 'cast (list nat) Any [3, 2, 1, 0]' '3 theorems' 'lisp.countdown'; do
    grep -qF "$v" example/out.log || { echo "lisp example: no $v"; cat example/out.log; exit 1; }
  done
fi
