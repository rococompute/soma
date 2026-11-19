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
Inductive wrap (T : Type) : Type := W0 : wrap T | W1 : T -> wrap T | Wtag : X.A -> wrap T.
Definition wrap_up (w : wrap nat) : wrap Any := cast (wrap nat) (wrap Any) w.
Definition wrap_down (w : wrap Any) : wrap nat := cast (wrap Any) (wrap nat) w.
End Make.
Module NatArg. Definition A := nat. End NatArg.
Module BoolArg. Definition A := bool. End BoolArg.
Module N := Make NatArg.
Module B := Make BoolArg.
Module N2 := Make NatArg.
Module Alias := N.
Definition roundtrip (_ : unit) : N.box := cast Any N.box (N.inject 2).
Definition wrong (_ : unit) : B.box := cast Any B.box (N.inject 2).
Definition wrong_inside (_ : unit) : B.box := B.project (N.inject 2).
Definition aliased (_ : unit) : Alias.box := Alias.project (N.inject 2).
Definition second_wrong (_ : unit) : N2.box := N2.project (N.inject 2).
Definition wrapped_roundtrip (_ : unit) : N.wrap nat := N.wrap_down (N.wrap_up (N.W1 nat 2)).
Definition wrapped_roundtrip2 (_ : unit) : N2.wrap nat := N2.wrap_down (N2.wrap_up (N2.W1 nat 2)).
Goal roundtrip tt = N.B1 2. Proof. reflexivity. Qed.
Goal wrong tt = raise. Proof. reflexivity. Qed.
Goal wrong_inside tt = raise. Proof. reflexivity. Qed.
Goal aliased tt = N.B1 2. Proof. reflexivity. Qed.
Goal second_wrong tt = raise. Proof. reflexivity. Qed.
Goal wrapped_roundtrip tt = N.W1 nat 2. Proof. reflexivity. Qed.
Goal wrapped_roundtrip2 tt = N2.W1 nat 2. Proof. reflexivity. Qed.
Extract Inductive unit => "unit" [ "()" ].
Extraction "Functor" roundtrip wrong wrong_inside aliased second_wrong wrapped_roundtrip wrapped_roundtrip2.
