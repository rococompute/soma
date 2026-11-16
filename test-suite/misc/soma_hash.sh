#!/usr/bin/env bash

# The hashes of a definition (vernac/somaHash.ml): of what the kernel checked,
# not of the file. soma hash prints CONTRACT WITNESS NAME, and what it assumes.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"
# its own shared build store (topbin/soma.ml): one kept from an earlier run
# would skip the compiles this test counts
export SOMA_CACHE="$TMP/.soma-store"

# contract FILE NAME, witness FILE NAME, assumes FILE NAME
line() { soma hash "$1" 2>/dev/null | awk -v n="$2" '$3 == n'; }
contract() { line "$1" "$2" | cut -d' ' -f1; }
witness() { line "$1" "$2" | cut -d' ' -f2; }
same() { [ "$2" = "$3" ] || { echo "should be the same, $1: $2 / $3"; exit 1; }; [ -n "$2" ] || { echo "no hash: $1"; exit 1; }; }
differ() { [ "$2" != "$3" ] || { echo "should differ, $1: $2"; exit 1; }; [ -n "$2" ] && [ -n "$3" ] || { echo "no hash: $1"; exit 1; }; }

# * What is not in the term is not in the hash
echo 'double (n : nat) : nat := n + n.' > a.soma
A="$(contract a.soma a.double)"
AW="$(witness a.soma a.double)"
[ "${#A}" = 64 ] || { echo "not 64 hexadecimal digits: $A"; exit 1; }
cat > a.soma <<'EOT'
(* a comment, and the definition on other lines *)


double (m : nat) : nat :=
    m + m.
EOT
same 'comments, layout, a binder name' "$A" "$(contract a.soma a.double)"
same 'and the witness' "$AW" "$(witness a.soma a.double)"
# which file, or folder, it is in
mkdir -p elsewhere/deep
echo 'double (n : nat) : nat := n + n.' > elsewhere/deep/other.soma
same 'another file, another folder' "$A" "$(cd elsewhere/deep && contract other.soma other.double)"
# universes, whose names have the file's in them
echo 'pairs (A B : Type) : Type := prod A B.' > u1.soma
echo 'pairs (A B : Type) : Type := prod A B.' > other_name.soma
same 'a universe of another file' "$(contract u1.soma u1.pairs)" "$(contract other_name.soma other_name.pairs)"
# what it is, is in it
echo 'double (n : nat) : nat := n + n + n.' > a.soma
differ 'another body' "$A" "$(contract a.soma a.double)"
echo 'double (n : nat) : nat := n + n.' > a.soma

# the format is stable: a change to this is a new format, and says so in it
same 'the hash of this definition, in soma-hash 1' "$A" \
  "549c4f409caaeb83f727f296841372b2470fd9a61c2f174af02eb7586caddfca"

# * What mentions a definition, mentions its hash
printf 'Import a.\nquad (n : nat) : nat := double (double n).\n' > b.soma
B="$(contract b.soma b.quad)"
echo 'double (n : nat) : nat := 2 * n.' > a.soma
differ 'what it mentions changed' "$B" "$(contract b.soma b.quad)"
echo 'double (n : nat) : nat := n + n.' > a.soma
same 'and back' "$B" "$(contract b.soma b.quad)"
printf 'Import a.\nquad (m : nat) : nat :=\n  double (double m).\n' > b.soma
same 'the same term, written otherwise' "$B" "$(contract b.soma b.quad)"
# both are listed: the file, and what it imports
soma hash b.soma | grep -q ' a.double$'
soma hash b.soma | grep -q ' b.quad$'

# * Another proof of a statement: the witness, and not the contract
echo 'zero : nat := 0.' > p.soma
printf 'Theorem t : forall n : nat, n = n.\nProof. intro n. reflexivity. Qed.\n' > p.exp
printf 'Theorem u2 : 1 = 1.\nProof. exact (t 1). Qed.\n' > q.exp
printf 'Import p.\nkeep : nat := 1.\n' > q.soma
T="$(contract q.soma p.t)"; TW="$(witness q.soma p.t)"
U="$(contract q.soma q.u2)"; UW="$(witness q.soma q.u2)"
printf 'Theorem t : forall n : nat, n = n.\nProof. intro n. destruct n; reflexivity. Qed.\n' > p.exp
same 'another proof: its contract' "$T" "$(contract q.soma p.t)"
differ 'another proof: its witness' "$TW" "$(witness q.soma p.t)"
same 'another proof: what mentions it, its contract' "$U" "$(contract q.soma q.u2)"
differ 'another proof: what mentions it, its witness' "$UW" "$(witness q.soma q.u2)"

# * A proof that rests on more is another contract: Soma's logic is inconsistent
# once unknown is used, and a theorem proves what its assumptions leave of it
printf 'Theorem st : 1 = 1.\nProof. reflexivity. Qed.\n' > r.exp
echo 'r0 : nat := 0.' > r.soma
printf 'Import r.\nTheorem up : 1 = 1.\nProof. exact st. Qed.\n' > s.exp
printf 'Import r.\ns0 : nat := 0.\n' > s.soma
R="$(contract s.soma r.st)"; UP="$(contract s.soma s.up)"
if line s.soma r.st | grep -q assumes; then echo "assumes nothing:"; line s.soma r.st; exit 1; fi
printf 'Axiom cheat : 1 = 1.\nTheorem st : 1 = 1.\nProof. exact cheat. Qed.\n' > r.exp
differ 'a proof that begins to rest on an axiom: its contract' "$R" "$(contract s.soma r.st)"
differ 'and what mentions it, its contract' "$UP" "$(contract s.soma s.up)"
line s.soma r.st | grep -q 'assumes r.cheat$'
line s.soma s.up | grep -q 'assumes r.cheat$'
# a gradual elaboration is in the term, and what it uses is assumed
echo 'g (x : Any) : nat := x.' > g.soma
line g.soma g.g | grep -q 'assumes .*Gradual.cast'
echo 'g (x : nat) : nat := x.' > g.soma
if line g.soma g.g | grep -q 'assumes'; then echo "static code assumes nothing:"; line g.soma g.g; exit 1; fi

# * Names of constructors are in a type, and its own is not: two types of two
# constructors each are not one type, however alike
echo 'Inductive color := Red | Green.' > c1.soma
echo 'Inductive shade := Red | Green.' > c2.soma
echo 'Inductive color := Red | Blue.' > c3.soma
same 'a type by another name' "$(contract c1.soma c1.color)" "$(contract c2.soma c2.shade)"
differ 'another constructor' "$(contract c1.soma c1.color)" "$(contract c3.soma c3.color)"
# a type's definition is in what uses it
printf 'Import c1.\nf (x : color) : nat := match x with Red => 0 | Green => 1 end.\n' > uses.soma
printf 'Import c3.\nf (x : color) : nat := match x with Red => 0 | Blue => 1 end.\n' > uses3.soma
differ 'a function of another type' "$(contract uses.soma uses.f)" "$(contract uses3.soma uses3.f)"
# recursive and mutual definitions
cat > m.soma <<'EOT'
Inductive tree := Node (k : forest) with forest := Nil | Cons (t : tree) (f : forest).
Fixpoint even (n : nat) : bool := match n with 0 => true | Succ m => odd m end
with odd (n : nat) : bool := match n with 0 => false | Succ m => even m end.
EOT
[ -n "$(contract m.soma m.tree)" ] && [ -n "$(contract m.soma m.forest)" ] && [ -n "$(contract m.soma m.even)" ]
differ 'two members of a block' "$(contract m.soma m.even)" "$(contract m.soma m.odd)"
differ 'two members of a block' "$(contract m.soma m.tree)" "$(contract m.soma m.forest)"

# * Foreign code: a module's bytes are in the hash of what calls it
# (a module, and the same with a custom section added)
printf '\0asm\1\0\0\0\1\7\1\140\2\176\176\1\176\3\2\1\0\7\7\1\3add\0\0\12\11\1\7\0\40\0\40\1\174\13' > w.wasm
printf 'add : Any -> Any -> Any.\n' > w.definition
printf 'Import w.\nuse : Any := add.\n' > wuse.soma
W="$(contract wuse.soma wuse.use)"
[ -n "$W" ]
printf '\0\4\1x\1\2' >> w.wasm
differ 'a module with other bytes' "$W" "$(contract wuse.soma wuse.use)"
# an OCaml module's source likewise
printf 'let f x = x\n' > o.ml
printf 'f : string -> string.\n' > o.definition
printf 'Import o.\nuseo : string -> string := f.\n' > ouse.soma
O="$(contract ouse.soma ouse.useo)"
[ -n "$O" ]
printf 'let f x = x ^ "!"\n' > o.ml
differ 'an OCaml module with other source' "$O" "$(contract ouse.soma ouse.useo)"

# * Another proof compiles nothing else; the hashes say what it now rests on,
# of the compiled files as they are
mkdir cached; cd cached
echo 'Axiom unused : 1 = 1.' > a.soma
printf 'Theorem t : 1 = 1.\nProof. reflexivity. Qed.\n' > a.exp
printf 'Import a.\nused : 1 = 1 := t.\n' > b.soma
printf 'Import b.\nfinal : 1 = 1 := used.\n' > main.soma
soma build main.soma > out.log 2>&1 || { cat out.log; exit 1; }
BVO="$(cksum .soma-cache/b.vo)"
C="$(contract main.soma main.final)"
printf 'Theorem t : 1 = 1.\nProof. exact unused. Qed.\n' > a.exp
soma build main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q 'Compiling a.soma' out.log
if grep -q 'Compiling b.soma' out.log; then echo "another proof compiled an importer"; cat out.log; exit 1; fi
[ "$BVO" = "$(cksum .soma-cache/b.vo)" ]
differ 'a cached importer of what now rests on an axiom' "$C" "$(contract main.soma main.final)"
line main.soma main.final | grep -q 'assumes a.unused$'
# a statement is not a proof
printf 'Theorem t : 2 = 2.\nProof. reflexivity. Qed.\nTheorem s : 1 = 1.\nProof. reflexivity. Qed.\n' > a.exp
if soma build main.soma > out.log 2>&1; then echo "an importer took a statement that went away"; exit 1; fi
grep -q 'Compiling b.soma' out.log
cd "$TMP"

# * Equal hashes say two definitions are the same, and not that a file imports
# the same: a notation is not in the kernel's terms
printf 'x1 : nat := 5.\nx2 : nat := 6.\nNotation "!!" := x1.\n' > nota.soma
printf 'Import nota.\nn : nat := !!.\nn.\n' > usen.soma
X="$(contract usen.soma nota.x1)"
sed -i.bak 's/:= x1\./:= x2./' nota.soma
same 'a notation is not a definition' "$X" "$(contract usen.soma nota.x1)"
differ 'but what it elaborated to is' "$(contract usen.soma usen.n)" "$X"
soma build -v usen.soma 2>&1 | grep -q '= 6'

# * A dependency's definition is the same definition, under its name
mkdir -p lib top
printf '[project]\nname = "lib"\nversion = "0.1.0"\n' > lib/soma.toml
echo 'double (n : nat) : nat := n + n.' > lib/a.soma
printf '[project]\nname = "top"\nversion = "0.1.0"\n[dependencies]\n"o/lib" = { path = "../lib" }\n' > top/soma.toml
printf 'Import lib.a.\nz : nat := double 1.\n' > top/main.soma
same 'as a dependency, as a file' "$A" "$(cd top && contract main.soma lib.a.double)"
same 'and built on its own' "$A" "$(cd lib && contract a.soma a.double)"
# no hash without a check
echo 'bad : nat := true.' > bad.soma
if soma hash bad.soma > out.log 2>&1; then echo "hashed what does not check"; exit 1; fi
