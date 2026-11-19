(* Acceptance fixture for complete modular gradual type identity.
   Both goals are proved by the kernel. Baseline monolithic extraction then
   fails the first roundtrip at run time because Make.box and N.box have
   different strings. A shared marker/registry cannot repair that identity.
   Run: rocq c -q functor_identity.v
        ocamlc Functor.mli Functor.ml functor_identity.ml -o check.exe
        ./check.exe
   Exported physical brands now make the executable agree with the kernel
   across module/functor signatures, applications and aliases. *)
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
Module Type INPUT.
Inductive t : Type := T0 : t | T1 : nat -> t.
End INPUT.
Module Input : INPUT.
Inductive t : Type := T0 : t | T1 : nat -> t.
End Input.
Module Input2 : INPUT.
Inductive t : Type := T0 : t | T1 : nat -> t.
End Input2.
Module InputAlias := Input.
Module InputReexport. Include Input. End InputReexport.
Module UseInput (X : INPUT).
Definition inject (x : X.t) : Any := cast X.t Any x.
Definition project (x : Any) : X.t := cast Any X.t x.
End UseInput.
Module U := UseInput Input.
Module UA := UseInput InputAlias.
Module UR := UseInput InputReexport.
Module U2 := UseInput Input2.
Definition argument_roundtrip (_ : unit) : Input.t := U.project (U.inject (Input.T1 2)).
Definition argument_alias (_ : unit) : InputAlias.t := UA.project (U.inject (Input.T1 2)).
Definition argument_reexport (_ : unit) : InputReexport.t := UR.project (U.inject (Input.T1 2)).
Definition argument_wrong (_ : unit) : Input2.t := U2.project (U.inject (Input.T1 2)).
Module Outer (X : ARG).
Module Inner (Y : ARG).
Inductive cell : Type := C0 : cell | C1 : X.A -> Y.A -> cell.
Definition inject (x : X.A) (y : Y.A) : Any := cast cell Any (C1 x y).
Definition project (value : Any) : cell := cast Any cell value.
End Inner.
End Outer.
Module OuterN := Outer NatArg.
Module OuterN2 := Outer NatArg.
Module NN := OuterN.Inner NatArg.
Module NN2 := OuterN2.Inner NatArg.
Module NNAlias := NN.
Definition nested_roundtrip (_ : unit) : NN.cell := NN.project (NN.inject 2 3).
Definition nested_alias (_ : unit) : NNAlias.cell := NNAlias.project (NN.inject 2 3).
Definition nested_wrong (_ : unit) : NN2.cell := NN2.project (NN.inject 2 3).
Goal roundtrip tt = N.B1 2. Proof. reflexivity. Qed.
Goal wrong tt = raise. Proof. reflexivity. Qed.
Goal wrong_inside tt = raise. Proof. reflexivity. Qed.
Goal aliased tt = N.B1 2. Proof. reflexivity. Qed.
Goal second_wrong tt = raise. Proof. reflexivity. Qed.
Goal wrapped_roundtrip tt = N.W1 nat 2. Proof. reflexivity. Qed.
Goal wrapped_roundtrip2 tt = N2.W1 nat 2. Proof. reflexivity. Qed.
Goal argument_roundtrip tt = Input.T1 2. Proof. reflexivity. Qed.
Goal argument_alias tt = InputAlias.T1 2. Proof. reflexivity. Qed.
Goal argument_reexport tt = InputReexport.T1 2. Proof. reflexivity. Qed.
Goal argument_wrong tt = raise. Proof. reflexivity. Qed.
Goal nested_roundtrip tt = NN.C1 2 3. Proof. reflexivity. Qed.
Goal nested_alias tt = NNAlias.C1 2 3. Proof. reflexivity. Qed.
Goal nested_wrong tt = raise. Proof. reflexivity. Qed.
Extract Inductive unit => "unit" [ "()" ].
Extraction "Functor" roundtrip wrong wrong_inside aliased second_wrong wrapped_roundtrip wrapped_roundtrip2
  argument_roundtrip argument_alias argument_reexport argument_wrong
  nested_roundtrip nested_alias nested_wrong.
