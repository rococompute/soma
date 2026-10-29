(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * List literals, part of the Soma prelude

    [[1, 2, 3]] is [cons 1 (cons 2 (cons 3 nil))], and lists print that
    way. Stdlib's [ListNotations] ([[1; 2; 3]]) can still be imported
    alongside. *)

Declare Scope soma_list_scope.
Notation "[ ]" := nil (format "[ ]") : soma_list_scope.
Notation "[ x ]" := (cons x nil) : soma_list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ,  '/' y ,  '/' .. ,  '/' z ']' ]") : soma_list_scope.
Open Scope soma_list_scope.
