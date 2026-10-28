(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Run-time errors of gradual programs: what went wrong when a term
    evaluates to (or contains) [err], the [raise] of [Corelib.Gradual]. *)

open EConstr

(** Does [err] occur in this term? *)
val mentions_err : Environ.env -> Evd.evar_map -> constr -> bool

(** The term with its partial strings, ending in something else than
    [EmptyString] (a [raise]), as ["abc" ++ rest] (with
    [lightlang.string.append], when registered) *)
val partial_strings : Environ.env -> Evd.evar_map -> constr -> constr

(** The message for a term that evaluated to an [err], from the casts that
    failed while evaluating [original] ({!Gradual.failures}): "expected a
    string, but got 42 : nat". Without failed casts, the [err] is a
    [raise] of the program, and the message says where. *)
val runtime_error : Environ.env -> Evd.evar_map -> original:constr ->
  failures:Gradual.failure list -> Pp.t
