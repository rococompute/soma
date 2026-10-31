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

(** Is this type, in weak head normal form, the unknown type [?]? *)
val is_unknown_type : env -> Evd.evar_map -> types -> bool

(** Does [?] (an [Any], or an [unk] of any type) occur in this term, as
    written, without unfolding constants? *)
val mentions_unknown : env -> Evd.evar_map -> types -> bool

(** [consistent ~cumul env sigma a b]: [a] and [b] are equal up to the
    unknown term, and up to cumulativity from [a] to [b] where Rocq allows
    it when [cumul] (the default). *)
val consistent : ?cumul:bool -> env -> Evd.evar_map -> types -> types -> bool

(** [inconsistency env sigma a b] is [None] when [a] and [b] are
    consistent, and otherwise the first pair of subterms (in their
    environment) whose heads are not consistent. *)
val inconsistency : ?cumul:bool -> env -> Evd.evar_map -> types -> types ->
  (env * types * types) option

(** [Above_gradual (env, sigma, inferred, expected, ty)]: no cast from
    [inferred] to [expected] could be built, because [ty] (one of them) lives
    above the universe of gradual types. Raised by [coerce_to_type]. *)
exception Above_gradual of env * Evd.evar_map * types * types * types

(** [with_index_defaulting b f] runs [f] with the undetermined indices of
    casts from [?] to inductive types defaulted to [?] or not ([true]
    outside of [match]); parameters are always. *)
val with_index_defaulting : bool -> (unit -> 'a) -> 'a

(** [with_gradual_scrutinee f] runs [f], the elaboration of a [match];
    [set_gradual_scrutinee env sigma scrutinees] records that a scrutinee is
    a cast from [?]: the branches of the [match] may then be at another index
    of the same inductive family than expected, and are cast through [?]. *)
val with_gradual_scrutinee : (unit -> 'a) -> 'a
val set_gradual_scrutinee : env -> Evd.evar_map -> constr list -> unit
val is_gradual_scrutinee : unit -> bool

(** [unknown_at env sigma ty] is the unknown term [?_ty], when Gradual Typing
    is enabled and [ty] lives in the universe of gradual types. *)
val unknown_at : env -> Evd.evar_map -> types -> (Evd.evar_map * constr) option

(** [default_leftover_implicits env sigma ~typ body] sets to [?] the
    implicit arguments (of functions, and of the inductive types of match
    scrutinees) that are still undefined in [body], when Gradual Typing is
    enabled, [body] itself mentions a gradual primitive, and they do not
    occur in [typ] (or the type of [body]). *)
val default_leftover_implicits : env -> Evd.evar_map -> typ:types option -> constr -> Evd.evar_map

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

(** Fake evidence: [unknown P], [err P] or [cast A P v] for a proposition
    [P], which inhabits any statement. [env] is where [P] is, and [within]
    the constant whose transparent body has it, when not the proof itself. *)
type fake = { kind : Gradual.kind; env : env; prop : Constr.t; within : Names.Constant.t option }

(** [proof_fake_evidence env ~typ ~body] is the first fake evidence of the
    proof [body] of [typ]: in [body], or in the transparent bodies of the
    constants it uses, unless it occurs in the statement [typ] itself (a
    theorem about such a term). Gradual primitives at other types than
    propositions are what a theorem about a gradual program is about, and
    are not evidence. [None] when there is none, or when no gradual
    primitive is registered. *)
val proof_fake_evidence : env -> typ:Constr.types -> body:Constr.constr -> fake option

(** {6 What a value of type [Any] may be} *)

(** A static type a value was made an [Any] from, and the definition where
    it was *)
type origin = { otype : Constr.types; made_in : Names.Constant.t option }

(** A cast from [Any] to [target] of [value], which may have been made from
    each of [failing], which [target] is not consistent with, so that the
    cast fails for it, and of [fitting] *)
type may_fail = {
  env : env;
  value : Constr.t;
  target : Constr.types;
  failing : origin list;
  fitting : origin list;
}

(** The casts from [Any] of [body] that fail for some of what their value
    may be, following it back through [match]es and definitions *)
val casts_that_may_fail : env -> Constr.t -> may_fail list

