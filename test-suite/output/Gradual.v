(* Elaboration of gradual CIC: casts are inserted where types are only
   consistent, following GCIC^G *)
From Corelib.Gradual Require Import Gradual.

Definition succ_dyn (x : Dyn) : nat := x + 1.
Print succ_dyn.

(* a function of unknown type is cast to the germ Dyn -> Dyn *)
Definition apply3 (g : Dyn) : nat := g 3.
Print apply3.

(* Omega, as in the paper *)
Definition delta := fun x : Dyn => x x.
Print delta.
Definition omega : Dyn := delta delta.
Print omega.

(* a type of unknown sort is cast to a universe *)
Definition T (X : Dyn) : Type := X -> X.
Print T.

(* the expected type list Dyn reaches both elements *)
Definition mixed : list Dyn := cons 1 (cons true nil).
Print mixed.

Definition mixed_pair : Dyn * Dyn := (1, true).
Print mixed_pair.

(* the inserted casts compute *)
Eval lazy in succ_dyn 41.
Eval lazy in succ_dyn true.
Eval lazy in apply3 negb.
Eval lazy in (unk : nat -> bool).
Eval lazy in 2 + unk.

(* static errors are still errors *)
Fail Definition bad : nat := true.
