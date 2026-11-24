(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: functions that a program calls and that are not Soma code, the
    exports of a WebAssembly module (plugins/soma_wasm). They are
    parameters, opaque to the kernel, which never computes them; Soma
    computes them when it evaluates a term (a bare term, Explore). *)

(** [!step env sigma c]: [c] with the calls whose arguments are values
    replaced by what they return, or [None] when there is none. Set by the
    plugin that knows the functions. *)
val step : (Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t option) ref

(** [!describe c]: what [c] is, when it is such a function ("add.wasm's
    add: (i64, i64) -> i64") *)
val describe : (Names.Constant.t -> Pp.t option) ref

(** What an image needs to call [c], when it is such a function: the
    module's file, the export's name, and, for each argument and the
    result, the declared type and the module's ("N", "i64") *)
type image_call = {
  module_file : string;
  export : string;
  params : (string * string) list;
  result : string * string;
}

val image : (Names.Constant.t -> image_call option) ref

(** [evaluate ~reduce env sigma c]: [c], evaluated by [reduce], with its
    foreign calls computed, and evaluated again, until there is none left
    that can be *)
val evaluate : reduce:(EConstr.t -> EConstr.t) -> Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t

(** OCaml modules (plugins/soma_ocaml): FILE.ml, which FILE.definition
    declares, or a library's module, which a .definition next to no module
    declares (async.definition: Async). Soma never computes them; a program
    that uses one is built with it, by OCaml (toplevel/somaOcaml.ml). *)

(** What a declaration is in OCaml: a type with that many parameters
    ([html : Type -> Type] is ['a html]), or a value of that OCaml type,
    whose arguments are given by position, and the labels of its
    arguments in OCaml (a named argument, [forall (attrs : ...), ...], is
    OCaml's [~attrs]) *)
type native_variant_case = {
  case_tag : string;
  case_payload : string option;
  case_is_function : bool;
}

type native_variant = {
  variant_namespace : string;
  variant_name : string;
  variant_source : string;
  variant_cases : native_variant_case list;
}

type native_callable = {
  callable_namespace : string;
  callable_name : string;
  callable_source : string;
  callable_arguments : string list;
  callable_labels : string option list;
  callable_result : string;
}

type native_operation =
  | NativeValue of string
  | NativeGet of string
  | NativeSet of string
  | NativeBuild of string list
  | NativeCopy of string list
  | NativeCallableApply of native_callable option
  | NativeVariantView of native_variant option
  | NativeVariantBuild of string * native_variant option
  | NativeExternalValue of string
  | NativeConstructorTag of string * int
  | NativeConstructorCase of string * int
  | NativeExternalConstant of string
  | NativeCallableWrap of native_callable option
  | NativeExternalLiteralConstant of string * string
  | NativeExternalException of string
  | NativeConstructorBuild of string * int
  | NativeExternalLiteralCallback of string * string * int

type native_callback = {
  namespace : string;
  name : string;
  arguments : string list;
  result : string;
  labels : string option list;
  operation : native_operation;
}

type native_record_field = {
  field_name : string;
  field_type : string;
  field_mutable : bool;
}

type native_record = {
  record_namespace : string;
  record_name : string;
  record_source : string;
  record_fields : native_record_field list;
}

type native_logical_record = {
  logical_type : string;
  logical_constructor : string;
  logical_projections : string list;
  logical_definitions : string list;
}

type ocaml_item =
  | OCamlType of int
  | OCamlValue of string * string option list
  | OCamlNativeOwnedRecord of native_record
  | OCamlNativeOwnedVariant of native_variant
  | OCamlNativeCallableType of native_callable
  | OCamlNativeType of string
  | OCamlNativeExternalFamily of string list * string
  | OCamlNativeCallback of native_callback
  | OCamlNativeImmutableRecord of native_record * native_logical_record
  | OCamlNativeParametricVariant of string list * native_variant
  | OCamlNativeParametricCallable of string list * native_callable

type ocaml_module = {
  ml_file : string option;          (** FILE.ml, absolute, or none: a library's module *)
  top : string;                     (** its name in OCaml: Web, Async *)
  libraries : string list;          (** the findlib libraries it uses *)
  items : (Names.Constant.t * string * ocaml_item) list;
  (** with their paths in it: Deferred.bind *)
}

(** the OCaml modules of the libraries loaded *)
val ocaml_modules : (unit -> ocaml_module list) ref

(** Canonical native declaration metadata, included in hashes and manifests. *)
val native_identity : ocaml_item -> string

(** Collision-free standalone record modules; fields retain declaration order. *)
val native_record_module : native_record -> string
val native_record_type : native_record -> string
val native_record_filename : native_record -> string
val native_record_ml : native_record -> string

(** Closed polymorphic variants borrow their native payloads without casts. *)
val native_variant_module : native_variant -> string
val native_variant_type : native_variant -> string
val native_variant_filename : native_variant -> string
val native_variant_ml : native_variant -> string
val native_variant_view_type : native_variant -> string
val native_variant_identity : native_variant -> string
val native_parametric_variant_ml : string list -> native_variant -> string
val native_parametric_variant_identity : string list -> native_variant -> string

val native_callable_module : native_callable -> string
val native_callable_type : native_callable -> string
val native_callable_filename : native_callable -> string
val native_callable_ml : native_callable -> string
val native_callable_identity : native_callable -> string

val native_parametric_callable_ml : string list -> native_callable -> string
val native_parametric_callable_identity : string list -> native_callable -> string
