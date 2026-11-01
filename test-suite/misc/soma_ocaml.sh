#!/usr/bin/env bash

# An OCaml module, FILE.ml, used through FILE.definition next to it, or a
# library's, declared by a .definition next to no module (theories/Soma/OCaml.v,
# plugins/soma_ocaml): each declaration is given an OCaml type, or
# refused, when the definition is compiled; Soma never computes them. Building the program with OCaml (toplevel/somaOcaml.ml)
# needs opam and is skipped here (SOMA_OCAML_BUILD=0); dev/ocaml-check.sh
# builds and runs the examples.

set -euo pipefail

export PATH=$BIN:$PATH
export SOMA_OCAML_BUILD=0

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

cat > greet.ml <<'EOT'
type greeting = string
let hello name = "Hello, " ^ name ^ "!"
let say g = print_endline g
let twice f x = f (f x)
EOT
cat > greet.definition <<'EOT'
OCaml Library "unix".
greeting : Type.
box : Type -> Type.
hello : string -> greeting.
say : greeting -> unit.
twice : forall {A}, (A -> A) -> A -> A.
pairs : forall {A}, list (A * box A) -> option (string -> bool).
EOT
cat > prog.soma <<'EOT'
Import greet.
main := say (hello (twice (fun s => s) "Soma")).
EOT
soma build prog.soma > out.log 2>&1 || { cat out.log; exit 1; }

# what soma explore says they are: their OCaml types
soma explore prog.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q "greet.ml's type Greet.greeting, opaque to Soma" out.log
grep -q "greet.ml's Greet.twice : ('a -> 'a) -> 'a -> 'a, which OCaml checks" out.log
grep -q "greet.ml's Greet.pairs : ('a \* 'a Greet.box) list -> (string -> bool) option" out.log

# a library's module: lib.definition, next to no module, declares Lib, its
# Soma modules being Lib's submodules, and its named arguments labels
cat > lib.definition <<'EOT'
OCaml Library "lib".
Module Deferred.
  t : Type -> Type.
  map : forall {A B}, t A -> forall (f : A -> B), t B.
End Deferred.
EOT
cat > uses.soma <<'EOT'
Import lib.
main := fun (d : Deferred.t nat) => Deferred.map d S.
EOT
soma explore uses.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q "OCaml's Lib.Deferred.map : 'a Lib.Deferred.t -> ('a -> 'b) -> 'b Lib.Deferred.t (~f by label)" out.log

# the kernel does not compute them: no proof goes through OCaml code
cat > prog.proof <<'EOT'
Theorem t : hello "x" = hello "x".
Proof.
  reflexivity.
Qed.
Theorem u : twice (fun s => s) "x" = "x".
Proof.
  reflexivity.
Qed.
EOT
if soma build prog.soma > out.log 2>&1; then echo "a proof computed through OCaml code"; exit 1; fi
rm prog.proof

# a type that OCaml does not have
echo 'count : nat -> unit.' >> greet.definition
if soma build prog.soma > out.log 2>&1; then echo "nat was given to OCaml"; exit 1; fi
grep -q 'count : (nat -> unit) is not given to OCaml: nat is no type of OCaml.' out.log
sed -i.bak '$d' greet.definition

echo 'any : Any -> unit.' >> greet.definition
if soma build prog.soma > out.log 2>&1; then echo "Any was given to OCaml"; exit 1; fi
grep -q 'Any has no OCaml type' out.log
sed -i.bak '$d' greet.definition

echo 'Shout : string -> string.' >> greet.definition
if soma build prog.soma > out.log 2>&1; then echo "OCaml was given a capitalized value"; exit 1; fi
grep -q 'which OCaml cannot name' out.log
sed -i.bak '$d' greet.definition

echo 'OCaml Library "bad name".' >> greet.definition
if soma build prog.soma > out.log 2>&1; then echo "a library's name was not checked"; exit 1; fi
grep -q 'is not the name of a findlib library' out.log
sed -i.bak '$d' greet.definition

# a definition defines nothing
echo 'defined := "x".' >> greet.definition
if soma build prog.soma > out.log 2>&1; then echo "a definition defined something"; exit 1; fi
grep -q 'defines nothing: defined is a definition' out.log
sed -i.bak '$d' greet.definition

# a Soma module that OCaml cannot name
printf 'Module lower.\n  x : string.\nEnd lower.\n' >> greet.definition
if soma build prog.soma > out.log 2>&1; then echo "OCaml was given a lowercase module"; exit 1; fi
grep -q 'lower is no name of an OCaml module' out.log
sed -i.bak '$d' greet.definition; sed -i.bak '$d' greet.definition; sed -i.bak '$d' greet.definition

# a definition next to both a module of WebAssembly and of OCaml
touch greet.wasm
if soma build prog.soma > out.log 2>&1; then echo "greet.wasm and greet.ml were not told apart"; exit 1; fi
grep -q 'is next to both greet.wasm and greet.ml' out.log
rm greet.wasm

# an OCaml module without its definition
mv greet.definition other.definition
if soma build prog.soma > out.log 2>&1; then echo "greet.ml was imported without its definition"; exit 1; fi
grep -q 'greet.ml has no greet.definition next to it' out.log
mv other.definition greet.definition

# soma extract: the program as an OCaml project, which dune builds without
# Soma; a main that is a string is printed
mkdir extracted && cd extracted
cat > shout.ml <<'EOT'
let shout s = String.uppercase_ascii s ^ "!"
EOT
cat > shout.definition <<'EOT'
shout : string -> string.
EOT
cat > prog.soma <<'EOT'
Import shout.
main : string := shout "hello from Soma".
EOT
soma extract prog.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q 'OCaml: extracted prog.soma into .*/prog-ocaml' out.log
for f in prog.ml prog.mli soma_bindings.ml soma_main.ml shout.ml dune dune-project prog.opam README.md; do
  [ -f "prog-ocaml/$f" ] || { echo "soma extract wrote no $f"; exit 1; }
done
grep -q 'fun a0 -> Shout.shout a0' prog-ocaml/soma_bindings.ml
if command -v dune > /dev/null; then
  (cd prog-ocaml && dune build --profile release 2> ../dune.log) || { cat dune.log; exit 1; }
  [ "$(prog-ocaml/_build/default/soma_main.exe)" = "HELLO FROM SOMA!" ]
fi
# again, into what it made: it may; into a directory of something else: it may not
soma extract prog.soma > out.log 2>&1 || { cat out.log; exit 1; }
mkdir mine && touch mine/notes
if soma extract prog.soma -o mine > out.log 2>&1; then echo "soma extract wrote over a directory it did not make"; exit 1; fi
grep -q 'is not empty, and soma extract did not make it' out.log
