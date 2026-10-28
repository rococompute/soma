(* Lightlang: the run-time error of a term that evaluates to a raise *)
From Lightlang Require Import Lightlang.

to_type (A : Type) (x : Any) : A := x.

(* different types *)
to_type string 42.
(* a function where data is expected *)
to_type nat (fun n : nat => n).
(* the same family at other indices *)
to_type (1 = 2) (eq_refl 1).
(* a partial value: the string as far as it was computed *)
greet_any (name : Any) := append "Hello, " name.
greet_any 42.
String.length (greet_any 42).
[1, 2] ++ [to_type nat true].
(* under a binder, the value is not known *)
(fun n : nat => append "x" (n : Any)).
(* a raise of the program *)
safe_div (a b : nat) : nat := match b with 0 => raise | _ => a / b end.
safe_div 7 0.
(* no raise, no error *)
to_type (1 = 1) (eq_refl 1).
safe_div 7 2.
