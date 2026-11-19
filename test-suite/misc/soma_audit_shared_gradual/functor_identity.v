(* Failing acceptance fixture for complete modular gradual type identity.
   Both goals are proved by the kernel. Baseline monolithic extraction then
   fails the first roundtrip at run time because Make.box and N.box have
   different strings. A shared marker/registry cannot repair that identity.
   Run: rocq c -q functor_identity.v
        ocamlc Functor.mli Functor.ml functor_identity.ml -o check.exe
        ./check.exe
   This is intentionally not a passing-suite assertion until identity IDs
   are exported through module/functor signatures and applications. *)
From Corelib.Gradual Require Import Gradual.
From Corelib Require Extraction.
Module Type ARG. Parameter A : Type. End ARG.
Module Make (X : ARG).
Inductive box : Type := B0 : box | B1 : X.A -> box.
Definition inject (x : X.A) : Any := cast box Any (B1 x).
Definition project (x : Any) : box := cast Any box x.
End Make.
Module NatArg. Definition A := nat. End NatArg.
Module BoolArg. Definition A := bool. End BoolArg.
Module N := Make NatArg.
Module B := Make BoolArg.
Definition roundtrip (_ : unit) : N.box := cast Any N.box (N.inject 2).
Definition wrong (_ : unit) : B.box := cast Any B.box (N.inject 2).
Definition wrong_inside (_ : unit) : B.box := B.project (N.inject 2).
Goal roundtrip tt = N.B1 2. Proof. reflexivity. Qed.
Goal wrong tt = raise. Proof. reflexivity. Qed.
Goal wrong_inside tt = raise. Proof. reflexivity. Qed.
Extract Inductive unit => "unit" [ "()" ].
Extraction "Functor" roundtrip wrong wrong_inside.
