# lean_facts

Soma's functions, and theorems about them proved in Lean. Soma checks
with Lean that each theorem proves what Soma declares, and then builds on
it.

```
soma build -v main.soma     5050, 6765, and main.proof checked
soma explore main.soma      lists the Lean theorems Soma takes on trust
```

```
soma.toml          the project: its name, version and description
series.soma        sum_to and fib, in Soma
facts.lean         theorems about them, in Lean: 2 * sum_to n = n * (n + 1), fib n <= 2 ^ n
facts.definition   what Soma takes facts.lean to prove
main.soma          computes with sum_to and fib
main.proof         sum_to n = n * (n + 1) / 2, and a bound on fib, from Lean's theorems
lean-toolchain     the Lean that compiles facts.lean (elan reads it)
```

## A Lean file, and its definition

`facts.definition`, next to `facts.lean`, declares what Soma takes
`facts.lean` to prove, in Soma's terms:

```
Import series.

sum_to_formula : forall n, 2 * sum_to n = n * (n + 1).
fib_le_pow : forall n, fib n <= 2 ^ n.
```

`facts.lean` proves them about Soma's own `sum_to` and `fib`, which Soma
translates to Lean, into a module `Soma` that `facts.lean` imports:

```lean
import Soma
open Soma.series

theorem sum_to_formula : ∀ n, 2 * sum_to n = n * (n + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    show 2 * ((m + 1) + sum_to m) = (m + 1) * (m + 1 + 1)
    grind
```

The translation of `series.soma`, which Soma writes for Lean:

```lean
def Soma.series.fib (n : Nat) : Nat :=
  (match n with
    | 0 => 0
    | m + 1 => (match m with
    | 0 => 1
    | k + 1 => ((Soma.series.fib k) + (Soma.series.fib (k + 1)))))
```

## What Soma checks

`Import facts.` compiles `facts.definition`, which Lean checks:

1. Soma translates the definitions that the statements use (`sum_to`,
   `fib`, and theirs) to Lean. `nat` is `Nat`, `+` is `+`, a `match` is a
   `match`, and a `Fixpoint` is a structural `def`. Lean must take
   them.
2. Lean compiles `facts.lean`, with the Lean of `lean-toolchain`.
3. For each declaration, Lean checks that `facts.lean`'s theorem of that
   name has the declared statement, as translated:
   `example : ∀ (n : Nat), 2 * Soma.series.sum_to n = n * (n + 1) := @sum_to_formula`.
4. `#print axioms` lists what the proof depends on. A theorem proved with
   `sorry` is refused.

What does not hold is an error when `main.soma` is built:

```
facts.definition: facts.lean does not prove what facts.definition declares:
Check.lean:6:69: error: Type mismatch
  sum_to_formula
has type
  ∀ (n : Nat), 2 * Soma.series.sum_to n = n * (n + 1)
but is expected to have type
  ∀ (n : Nat), Soma.series.sum_to n = n * (n + 1)

facts.definition: facts.lean's sum_to_formula is proved with sorry, which proves nothing.

about_strings : (forall s : string, ...) is not given to Lean:
the type Stdlib.Strings.String.string has no Lean counterpart Soma knows.
```

## What Soma trusts

Soma's kernel never sees Lean's proofs. To Soma, a theorem of
`facts.definition` is an axiom, and `main.proof`'s theorems hold if it does.
That depends on Lean's kernel, on the axioms the proof uses, and on the
translation. `soma explore` lists each theorem with them:

```
Escape hatches, where static types are given up:
  facts.fib_le_pow
    is proved in Lean, by facts.lean's fib_le_pow ((∀ (n : Nat), ((Soma.series.fib n) ≤ (2 ^ n)))),
    which Soma's kernel takes as an axiom, Lean's proof using propext, Quot.sound
  facts.sum_to_formula
    is proved in Lean, by facts.lean's sum_to_formula (...), which Soma's kernel
    takes as an axiom, Lean's proof using propext, Classical.choice, Quot.sound
```

`grind` uses classical logic, which Soma's theorems then depend on, as
`Classical.choice` says. Rocq is consistent with it.

## What is translated

A fragment: `nat`, `bool`, lists, pairs and options; `+`, `*`, `-`, `/`,
`mod`, `^`, `max`, `min`; `=?`, `<=?`, `<?`, `&&`, `||`, `negb`; `length`,
`++`, `rev`, `map`, `fold_left`, `fold_right`, `seq`; `=`, `<=`, `<`, `>=`,
`>`, `~`, `/\`, `\/`, `<->`, `forall`, `exists`; `match` on these types; and
definitions, recursive ones as structural `Fixpoint`s. The rest is refused,
saying what. In Soma and Lean, `-` and `/` on `nat` are both truncated, and
`x / 0` is 0 in both, so the translated statement means what Soma's does.

## What it needs

`lean`, from elan (https://lean-lang.org/install). `lean-toolchain` says
which Lean: elan installs it if it is missing. Lean's standard library is
enough, without Mathlib.

## Not yet

- Soma's inductive types (`Inductive action := ...`), strings, integers.
- Theorems that Soma proves, given to Lean.
- A Lean project with dependencies (Mathlib): `facts.lean` is one file.
