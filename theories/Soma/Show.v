(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * [to_string], part of the Soma prelude

    [to_string] turns a value into a [string]. It is a type class method:
    each type has its own [to_string], an instance of [Show], and the one
    used is chosen from the type of the argument when the program is
    checked. A new type gets one with
    [#[export] Instance show_t : Show t := { to_string x := ... }.] *)

Require Import Soma.Strings.
From Stdlib Require Numbers.DecimalString NArith.BinNatDef ZArith.BinIntDef Lists.List.

Class Show (A : Type) := { to_string : A -> string }.

(** The instance is looked up only once the type is known. A definition
    whose argument type is unknown, like [Definition greet name :=
    to_string name], then takes the instance as an argument (see
    [Automatic Generalization]) instead of committing to the first
    instance found. *)
#[export] Hint Mode Show + : typeclass_instances.

#[export] Instance show_string : Show string := { to_string s := s }.

#[export] Instance show_bool : Show bool :=
  { to_string b := if b then "true" else "false" }.

(** Numbers, in decimal *)

#[export] Instance show_nat : Show nat :=
  { to_string n := DecimalString.NilZero.string_of_uint (Nat.to_uint n) }.

#[export] Instance show_N : Show BinNums.N :=
  { to_string n := DecimalString.NilZero.string_of_uint (BinNatDef.N.to_uint n) }.

#[export] Instance show_Z : Show BinNums.Z :=
  { to_string z := DecimalString.NilZero.string_of_int (BinIntDef.Z.to_int z) }.

(** [[1,2,3]]: the elements' [to_string], between brackets, separated by
    commas. Strings are not quoted, so [["a", "b"]] is [[a,b]]. *)
#[export] Instance show_list {A} `{Show A} : Show (list A) :=
  { to_string l :=
      append "[" (append (String.concat "," (List.map to_string l)) "]") }.
