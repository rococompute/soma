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

type native_export_pattern =
  | Export_name of string
  | Export_tuple of native_export_pattern list
  | Export_record of string * string list


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
  | NativeAssertionFactory of int * int
  | NativeExternalThunkFactory of string * string
  | NativeVariantFactory of string * native_variant option
  | NativeDeferredFields of string list * string
  | NativeDefaultedFunction of string * native_callable
  | NativeBoundBooleanFunction of string * native_callable * string * bool
  | NativeAssertionFunctionFactory of int * int
  | NativeExternalInsertedLiteralFunction of string * string * int * int
  | NativeExternalFieldsFunction of string * string list * string * int
  | NativeStaticFunction of bool * string * string * (native_operation * native_operation * string option list * string option list * string option list) option
  | NativeStaticCompositionScope of string * string * (native_operation * native_operation * string option list * string option list * string option list) option
  | NativeVariantFunction of string * native_variant option
  | NativeStaticApplication of string * string list * (native_operation * native_operation list * string option list * string option list) option
  | NativeStaticInvocation of native_static_expression * (native_static_term * string option list) option
  | NativeAssertionFunction of int * int
  | NativeEtaFunction of string * native_callable
  | NativeStaticData of string * string * string * string list * native_static_data option
  | NativeStaticInitialization of string * string list * (native_operation * native_operation list * string option list) option
  | NativePublishedValue of string * (string * string) option
  | NativeProjectedValue of string * string * (string * string) option
  | NativePublishedProjection of string * string * (string * string * string * string) option
  | NativeStaticInitializerExpression of native_static_expression * native_static_term option

and native_static_expression =
  | StaticArgument of int
  | StaticValue of string
  | StaticCall of string * native_static_expression list
  | StaticLambda of string * native_static_expression

and native_static_term =
  | NativeStaticArgument of int
  | NativeStaticValue of native_operation
  | NativeStaticCall of native_operation * native_static_term list * string option list
  | NativeStaticLambda of native_static_term * native_callable

and native_static_data =
  | DataReference of string
  | DataString of string
  | DataChar of char
  | DataWord of string
  | DataNat of string
  | DataFloat of string
  | DataBool of bool
  | DataUnit
  | DataPair of native_static_data * native_static_data
  | DataNil
  | DataCons of native_static_data * native_static_data
  | DataNone
  | DataSome of native_static_data
  | DataVariant of string * native_static_data option

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

type native_module_alias = {
  module_alias_namespace : string;
  module_alias_name : string;
  module_alias_target : string;
  module_alias_source : string;
  module_alias_order : int;
}

type native_algebraic_reexport = {
  reexport_namespace : string;
  reexport_name : string;
  reexport_source : string;
  reexport_owner : string;
  reexport_target : string;
  reexport_order : int;
  reexport_group : native_algebraic;
}

type native_value_reexport = {
  value_namespace : string;
  value_name : string;
  value_source : string;
  value_owner : string;
  value_module : string;
  value_order : int;
  value_callback : native_callback;
}

type native_variant_input = {
  input_namespace : string;
  input_name : string;
  input_argument : int;
  input_parameters : string list;
  input_domains : string list;
  input_result : string;
  input_variant : native_variant;
}
val native_variant_inputs : (unit -> native_variant_input list) ref
val variant_input : string -> string -> native_variant_input option

type native_algebraic_dependencies = {
  dependencies_namespace : string;
  dependencies_group : string;
  dependencies_members : (string * string list) list;
}
val native_algebraic_dependencies : (unit -> native_algebraic_dependencies list) ref

type native_algebraic_record_views = {
  views_namespace : string;
  views_group : string;
  views_records : (string * native_record_field list) list;
}
val native_algebraic_record_views : (unit -> native_algebraic_record_views list) ref

type native_source_type_body =
  | Source_record of native_record_field list
  | Source_variant of (string * string list) list
  | Source_alias of string
  | Source_group of native_algebraic
  | Source_exception of native_algebraic_payload

type native_source_type_reexport = {
  source_type_namespace : string;
  source_type_source : string;
  source_type_name : string;
  source_type_symbol : string;
  source_type_target : string;
  source_type_parameters : string list;
  source_type_body : native_source_type_body;
  source_type_order : int;
}

type native_binding_projection = {
  projection_namespace : string;
  projection_name : string;
  projection_source : string;
  projection_owner : string;
  projection_module : string;
  projection_callback : native_callback;
  projection_pattern : native_export_pattern;
  projection_text : string;
  projection_fields : (string * string) list;
  projection_order : int;
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
  | OCamlNativeOpenVariant of string * native_variant
  | OCamlNativeModuleAlias of native_module_alias
  | OCamlNativeAlgebraicReexport of native_algebraic_reexport
  | OCamlNativeModuleInclude of native_module_alias
  | OCamlNativeValueReexport of native_value_reexport
  | OCamlNativeSourceTypeReexport of native_source_type_reexport
  | OCamlNativeBindingProjection of native_binding_projection

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
val native_algebraic_reexport_ml : ?interface:bool -> native_algebraic_reexport -> string


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
val native_open_variant_ml : string -> native_variant -> string
val native_open_variant_identity : string -> native_variant -> string

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


type native_assembly = {
  assembly_owner : Names.Constant.t;
  assembly_namespace : string;
  assembly_source : string;
  assembly_value : string;
  assembly_pattern : native_export_pattern;
  assembly_pattern_text : string;
}
val native_assemblies : (unit -> native_assembly list) ref
val native_export_names : native_export_pattern -> string list
val native_export_identity : native_export_pattern -> string
val native_assembly_identity : native_assembly -> string

type native_static_exception = {
  static_exception_name : string;
  static_exception_symbol : string;
  static_exception_arguments : string list;
}
type native_static_exception_scope = {
  static_exception_owner : Names.Constant.t;
  static_exception_fields : native_static_exception list;
}
val native_static_exception_scopes : (unit -> native_static_exception_scope list) ref
val static_exceptions : Names.Constant.t -> native_static_exception list

type native_static_export_kind = Static_value | Static_type of int | Static_unpack
  | Static_projection of native_export_pattern
  | Static_application of native_callback list * string
type native_static_export = {
  static_export_kind : native_static_export_kind;
  static_export_name : string;
  static_export_reference : Names.GlobRef.t;
  static_export_symbol : string;
}
type native_static_assembly = {
  static_owner : Names.Constant.t;
  static_namespace : string;
  static_source : string;
  static_module : string;
  static_exports : native_static_export list;
}
val native_static_export_names : native_static_export -> string list
val native_static_assemblies : (unit -> native_static_assembly list) ref
type native_lexical_scope = {
  lexical_owner : Names.Constant.t;
  lexical_opens : string list;
  lexical_functor : (string * (string * string) list) option;
}
val native_lexical_scopes : (unit -> native_lexical_scope list) ref
val lexical_scope : Names.Constant.t -> native_lexical_scope option
val native_lexical_scope_identity : native_lexical_scope -> string
type native_lexical_environment = {
  environment_owner : Names.Constant.t;
  environment_prefix : (string * string * string) list;
  environment_prefix_layouts : string list;
  environment_modules : (string * string * string list) list;
  environment_locals : (string * string * string list) list;
}
val native_lexical_environments : (unit -> native_lexical_environment list) ref
val lexical_environment : Names.Constant.t -> native_lexical_environment option
val native_lexical_environment_identity : native_lexical_environment -> string

type native_static_postlude = {
  postlude_owner : Names.Constant.t;
  postlude_scopes : (string * string * string) list;
  postlude_layouts : string list;
}
val native_static_postludes : (unit -> native_static_postlude list) ref
val static_postlude : Names.Constant.t -> native_static_postlude option
val native_static_postlude_identity : native_static_postlude -> string

val native_static_assembly_identity : native_static_assembly -> string
val native_static_extraction_requests : (Names.GlobRef.t * bool) list ref
val native_runtime_references : Names.GlobRef.t list option ref
val native_static_extracted_names : (Names.GlobRef.t * bool * string * int) list ref
val native_public_extracted_values : string list option ref

type native_public_type_equation = {
  equation_name : string;
  equation_reference : Names.GlobRef.t;
  equation_symbol : string;
  equation_arity : int;
}
type native_public_types = {
  types_owner : Names.Constant.t;
  types_equations : native_public_type_equation list;
}
val native_public_types : (unit -> native_public_types list) ref
val native_public_extracted_types : string list option ref
val native_public_type_declarations : (Names.GlobRef.t * string * string) list ref
val public_type_equations : Names.Constant.t -> native_public_type_equation list

(* Flat field publications borrow an existing extracted record, without a wrapper. *)
type native_public_record = {
  record_public_owner : Names.Constant.t;
  record_public_receiver : Names.GlobRef.t;
  record_public_type : Names.GlobRef.t;
  record_public_fields : (string * int) list;
  record_public_symbols : string list;
}
val native_public_records : (unit -> native_public_record list) ref
val public_records : Names.Constant.t -> native_public_record list
val active_public_records : native_public_record list ref
val native_public_record_declarations : (Names.GlobRef.t * string * string * string) list ref

type native_public_application = {
  application_name : string;
  application_function : Names.GlobRef.t;
  application_arguments : Names.GlobRef.t list;
  application_symbols : string list;
  application_signature : string;
}
type native_public_assembly = {
  public_owner : Names.Constant.t;
  public_namespace : string;
  public_source : string;
  public_applications : native_public_application list;
}
val native_public_assemblies : (unit -> native_public_assembly list) ref
val native_public_assembly_identity : native_public_assembly -> string

val native_source_type_names : native_source_type_reexport -> string list
val native_source_type_reexport_ml : native_source_type_reexport -> string
val native_source_type_identity : native_source_type_reexport -> string

type native_extraction_type_equation = {
  reuse_owner : Names.Constant.t;
  reuse_namespace : string;
  reuse_source : string;
  reuse_reference : Names.GlobRef.t;
  reuse_symbol : string;
  reuse_target : string;
  reuse_parameters : int;
}
val native_extraction_type_equations : (unit -> native_extraction_type_equation list) ref
val active_extraction_type_equations : native_extraction_type_equation list ref
val printed_extraction_type_equations : (Names.GlobRef.t * bool * string * int) list ref
val extraction_type_equation_identity : native_extraction_type_equation -> string
val extraction_type_equations : Names.Constant.t -> native_extraction_type_equation list
