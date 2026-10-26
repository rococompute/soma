(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Elaboration of gradual CIC (GCIC{^G}) into the cast calculus.

    When the flag [Gradual Typing] is set and the gradual primitives are
    registered (see {!Gradual}), a term whose type is not convertible to the
    expected type is still accepted when the two types are {e consistent},
    i.e. equal up to occurrences of the unknown term. A cast is then
    inserted, which reduces to the term or to an error at run time.

    These functions are called by {!Coercion} as a last resort, after
    unification and coercions failed. *)

open EConstr
open Environ

(** Is gradual elaboration enabled? *)
val enabled : env -> bool

(** [consistent env sigma a b]: [a] and [b] are equal up to the unknown
    term. *)
val consistent : env -> Evd.evar_map -> types -> types -> bool

(** [coerce_to_type env sigma v ~inferred ~expected] casts [v : inferred]
    to [expected] if the types are consistent. *)
val coerce_to_type : env -> Evd.evar_map -> constr -> inferred:types -> expected:types ->
  (Evd.evar_map * constr * types) option

(** [coerce_to_product env sigma f ~inferred] casts a function of unknown
    type to [? -> ?]. *)
val coerce_to_product : env -> Evd.evar_map -> constr -> inferred:types ->
  (Evd.evar_map * constr * types) option

(** [coerce_to_sort env sigma t ~inferred] casts a type of unknown sort to a
    fresh universe. *)
val coerce_to_sort : env -> Evd.evar_map -> constr -> inferred:types ->
  (Evd.evar_map * constr * types) option
