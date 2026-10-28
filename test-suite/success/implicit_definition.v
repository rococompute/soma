(* Outside a proof, [f x := t.] is [Definition f x := t.] *)

x := 1.
Check x : nat.
add (a b : nat) := a + b.
Example add_ok : add 2 3 = 5 := eq_refl.
typed : nat -> nat := fun n => n.
Check typed : nat -> nat.

(* [:=] inside brackets does not make a definition: these are terms *)
Check (fun n => let m := n in m) 3.
Check id (A := nat).

(* As with Definition, a name is defined once, and recursion needs
   Fixpoint *)
Fail x := 2.
Fail loop n := match n with 0 => 0 | S m => loop m end.

Section S.
  Variable k : nat.
  plus_k a := a + k.
End S.
Check plus_k : nat -> nat -> nat.

Module M.
  inside := 5.
End M.
Check M.inside.
