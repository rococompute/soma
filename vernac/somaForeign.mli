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

type native_dispatch_pattern =
  | Dispatch_arguments of int
  | Dispatch_fields of string list
  | Dispatch_ignore of bool

type native_operation =
  | NativeValue of string
  | NativeGet of string
  | NativeGetFunction of string * string
  | NativeSet of string
  | NativeBuild of string list
  | NativeBuildEvaluating of string list * string list
  | NativeRecordFactory of string list * string list * string
  | NativeVariantDispatch of (string * native_dispatch_pattern * bool) list * string * bool
  | NativeCopy of string list
  | NativeCallableApply of native_callable option
  | NativeVariantView of native_variant option
  | NativeVariantBuild of string * native_variant option
  | NativeExternalValue of string
  | NativePrimitive of string * string option * bool
  | NativeConstructorTag of string * int
  | NativeConstructorCase of string * int
  | NativeExternalConstant of string
  | NativeCallableWrap of native_callable option
  | NativeCallableWrapFull of native_callable option
  | NativeExternalLiteralConstant of string * string
  | NativeExternalException of string
  | NativeConstructorBuild of string * int
  | NativeInlineGet of string * string
  | NativeInlineSet of string * string
  | NativeInlineBuild of string * string list
  | NativeExternalLiteralCallback of string * string * int
  | NativeExternalComposedValue of string * string * int * int
  | NativeExternalTransformedComposition of string * string * int * int * string * int
  | NativeSetFunction of string * string
  | NativeCallableApplyFunction of native_callable option
  | NativeFloatConstant of string
  | NativeExternalLiteralFunction of string * string * int

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


type native_algebraic_payload =
  | Constructor_arguments of string list
  | Constructor_record of native_record_field list

type native_algebraic_body =
  | Algebraic_record of native_record_field list
  | Algebraic_variant of (string * native_algebraic_payload) list

type native_algebraic = {
  algebraic_namespace : string;
  algebraic_name : string;
  algebraic_source : string;
  algebraic_members : (string * native_algebraic_body) list;
  algebraic_exceptions : (string * native_algebraic_payload) list;
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
  | OCamlNativeAlgebraic of native_algebraic * string
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
val native_algebraic_module : native_algebraic -> string
val native_algebraic_filename : native_algebraic -> string
val native_algebraic_type : native_algebraic -> string -> string
val native_algebraic_ml : native_algebraic -> string


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


(** A checked logical enumeration may share an existing native variant. *)
type native_enum_alias = {
  enum_constant : Names.Constant.t;
  enum_logical_type : string;
  enum_target : string;
  enum_constructors : string list;
  enum_source : string;
}
val native_enum_aliases : (unit -> native_enum_alias list) ref

(** Constructor payload representations for a reused checked native variant.
    Kept separate so existing enum metadata and serialized descriptors retain
    their exact shape. No conversion function or logical evaluator is added. *)
type native_variant_alias = {
  variant_alias_constant : Names.Constant.t;
  variant_alias_arguments : string list list;
}
val native_variant_aliases : (unit -> native_variant_alias list) ref

(** A checked immutable record reusing an existing native record ABI. *)
type native_record_alias = {
  record_alias_constant : Names.Constant.t;
  record_alias_logical_type : string;
  record_alias_target : string;
  record_alias_parameters : string list;
  record_alias_fields : native_record_field list;
  record_alias_projections : string list;
  record_alias_source : string;
}
val native_record_aliases : (unit -> native_record_alias list) ref
