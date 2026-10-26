(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Gradual CIC, normalization-sacrificing variant (GCIC{^G}).

    The kernel knows three axioms registered through the retroknowledge:
    - [unknown : forall A, A]       written [?{_A}] in the literature,
    - [err     : forall A, A]       written [err{_A}] (raise),
    - [cast    : forall A B, A -> B] written [<B <= A> t].

    Typing is plain CIC: these are axioms. Only reduction changes: this
    module implements the reduction rules of CastCIC on [constr], and the
    abstract machines ([CClosure], [Cbv], [Reductionops]) call into it.

    Following GCIC{^G}, casting into the unknown type does not go through a
    germ living one universe below, so [? -> ?] inhabits the same universe
    as [?]: the self-application [(fun x : ? => x x) (fun x : ? => x x)] is
    well typed and diverges. Graduality and conservativity over CIC are
    kept; normalization is the property that is given up. *)

open Names
open Constr

type kind = Retroknowledge.gradual_prim = GUnknown | GErr | GCast

val prim_to_string : kind -> string
val prim_of_string : string -> kind option

(** Arity of a primitive: the number of arguments its head rules need. *)
val arity : kind -> int

(** [kind_of env c] tells whether [c] is one of the registered gradual
    primitives. Cheap enough to be called on every constant. *)
val kind_of : Environ.env -> Constant.t -> kind option

(** Is any gradual primitive registered? Used to skip all gradual
    reasoning in environments that do not use it. *)
val enabled : Environ.env -> bool

val get : Environ.env -> kind -> Constant.t option

(** Check that a constant can be registered as the given primitive: it must
    be a monomorphic axiom with the expected type. *)
val check_registration : Environ.env -> kind -> Constant.t -> unit

(** {6 Views} *)

type head =
  | HProd of Name.t binder_annot * types * types
  | HSort of Sorts.t
  | HInd of pinductive * constr array
  | HUnknown (** [unknown X], the unknown type [?{_□}] *)
  | HErr (** [err X], the erroneous type *)
  | HOther (** neutral, or a head we do not know how to cast *)

(** [view_type env c] classifies a type in weak head normal form. *)
val view_type : Environ.env -> constr -> head

(** {6 Reduction rules} *)

(** [eta_unknown env k a] is the reduct of [k a] for [k] one of [GUnknown]
    or [GErr], when [a] (in whnf) is a product:
    [?{_forall x : A, B} ~> fun x : A => ?{_B}]. *)
val eta_unknown : Environ.env -> kind -> constr -> constr option

(** [reduce_cast env ~whnf a b t t_whnf] computes one step of
    [<b <= a> t], where [a] and [b] are in weak head normal form, [t] is the
    raw term and [t_whnf] its (lazily computed) weak head normal form.
    Returns [None] when the cast is a canonical form or is stuck. *)
val reduce_cast :
  Environ.env -> whnf:(constr -> constr) ->
  constr -> constr -> constr -> constr Lazy.t -> constr option

(** [inductive_indices env ci a] returns the indices of the inductive type
    [a] (in whnf) for a match described by [ci], or [None] when they cannot
    be computed. Used for [match ?{_I} return P with ... ~> ?{_P}]. *)
val inductive_indices : Environ.env -> case_info -> constr -> constr array option
