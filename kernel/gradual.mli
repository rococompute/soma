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

(** {6 Step budget}

    Reduction of gradual terms may not terminate. Each reduction step headed
    by a gradual primitive calls [step], which raises [Out_of_steps (k, n)]
    once [n] such steps have been made since the last [reset_steps]. [None]
    means no limit. *)

exception Out_of_steps of kind * int

val step : kind -> unit
val reset_steps : unit -> unit
val step_limit : unit -> int option
val set_step_limit : int option -> unit

(** {6 Failed casts}

    A cast that fails reduces to [err], which only keeps the type it stands
    for. [reduce_cast] records what failed: the type expected, the type of
    the value, and the value, for the error message of a term that
    evaluates to an [err]. A cast of an [err] is not a failure of its own,
    and is not recorded. Only the first few failures since the last
    [clear_failures] are kept. *)

type failure_reason =
  | FMismatch (** the types differ: [nat] and [string], data and a function *)
  | FIndices (** the same family at other indices: [1 = 1] and [1 = 2] *)

type failure = {
  expected : constr; (** the type the cast is to, in whnf *)
  actual : constr; (** the type of the value: with [FIndices], the type its
                       constructor builds *)
  value : constr; (** the value, as given to the cast *)
  reason : failure_reason;
}

val clear_failures : unit -> unit

(** The recorded failures, oldest first *)
val failures : unit -> failure list

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

(** Primitive types (registered in the retroknowledge). *)
type prim = PInt | PFloat | PString | PArray

type head =
  | HProd of Name.t binder_annot * types * types
  | HSort of Sorts.t
  | HInd of pinductive * constr array
  | HPrim of prim * constr array (** a primitive type, with the element type of arrays *)
  | HUnknown (** [unknown X], the unknown type [?{_□}] *)
  | HErr (** [err X], the erroneous type *)
  | HOther (** neutral, or a head we do not know how to cast *)

(** [is_unknown_type env c]: [c], in weak head normal form, is [?]. *)
val is_unknown_type : Environ.env -> constr -> bool

(** [prim_type env c] tells whether [c] is a registered primitive type. *)
val prim_type : Environ.env -> Constant.t -> prim option

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

(** [projection_type env p a scrut] is the type of [p scrut] where
    [scrut : a] and [a] is in whnf. Used for [?{_R}.(p) ~> ?{_T}]. *)
val projection_type : Environ.env -> Projection.t -> constr -> constr -> constr option
