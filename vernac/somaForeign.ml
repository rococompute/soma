(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let step : (Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t option) ref =
  ref (fun _ _ _ -> None)

let describe : (Names.Constant.t -> Pp.t option) ref = ref (fun _ -> None)

type image_call = {
  module_file : string;
  export : string;
  params : (string * string) list;
  result : string * string;
}

let image : (Names.Constant.t -> image_call option) ref = ref (fun _ -> None)

let evaluate ~reduce env sigma c =
  (* each round computes at least one call: a bound on them, not on time,
     which the gradual step budget and the module's own fuel see to *)
  let rec go c rounds =
    if rounds = 0 then c
    else match !step env sigma c with
      | None -> c
      | Some c' -> go (reduce c') (rounds - 1)
  in
  go c 100000

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

type native_algebraic_dependencies = {
  dependencies_namespace : string;
  dependencies_group : string;
  dependencies_members : (string * string list) list;
}
let native_algebraic_dependencies : (unit -> native_algebraic_dependencies list) ref = ref(fun()->[])

type native_source_type_body =
  | Source_record of native_record_field list
  | Source_variant of (string * string list) list
  | Source_alias of string
  | Source_group of native_algebraic

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

type ocaml_module = {
  ml_file : string option;
  top : string;
  libraries : string list;
  items : (Names.Constant.t * string * ocaml_item) list;
}

let ocaml_modules : (unit -> ocaml_module list) ref = ref (fun () -> [])

let native_record_module r =
  let key=Printf.sprintf "soma-native-owned-record-module-v1:%d:%s:%d:%s"
    (String.length r.record_namespace)r.record_namespace
    (String.length r.record_name)r.record_name in
  "Soma_owned_" ^ SomaMerkle.string key
let native_record_type r = native_record_module r ^ ".t"
let native_record_filename r = String.uncapitalize_ascii(native_record_module r)^".ml"
let native_record_ml r =
  "(* Generated by Soma: owned native record " ^ r.record_namespace ^ "." ^ r.record_name ^ ". *)\n" ^
  "type t = {\n" ^ String.concat "" (List.map(fun f->
    "  "^(if f.field_mutable then "mutable " else "")^f.field_name^" : "^f.field_type^";\n")r.record_fields)^"}\n" ^
  String.concat "" (List.filter_map(fun f->
    if f.field_mutable then None else Some
      ("let soma_get_"^f.field_name^" (value:t) = value."^f.field_name^"\n"))r.record_fields)

let native_variant_module v =
  let key=Printf.sprintf "soma-native-polyvariant-module-v1:%d:%s:%d:%s"
    (String.length v.variant_namespace)v.variant_namespace
    (String.length v.variant_name)v.variant_name in
  "Soma_variant_" ^ SomaMerkle.string key
let native_variant_type v = native_variant_module v ^ ".t"
let native_variant_filename v = String.uncapitalize_ascii(native_variant_module v)^".ml"
let native_variant_ml v =
  "(* Generated by Soma: closed native polymorphic variant " ^ v.variant_namespace ^ "." ^ v.variant_name ^ ". *)\n" ^
  "type t = [ " ^ String.concat " | " (List.map(fun c -> "`" ^ c.case_tag ^
    (match c.case_payload with None->""|Some t->" of ("^t^")"))v.variant_cases) ^ " ]\n"
let native_variant_view_type v =
  let payload c=Option.default "unit" c.case_payload,c.case_is_function in
  let arg(t,fn)=if fn then "("^t^")"else t in
  let rec fold=function
    | []->invalid_arg "empty native variant schema"
    | [c]->payload c
    | c::rest->"("^arg(payload c)^", "^arg(fold rest)^") result",false in
  fst(fold v.variant_cases)
let native_variant_identity v =
  String.concat "\n" (["native-owned-polyvariant";v.variant_namespace;v.variant_name;native_variant_type v] @
    List.map(fun c->Printf.sprintf "%S %b %s" c.case_tag c.case_is_function
      (match c.case_payload with None->"nullary"|Some t->Printf.sprintf "payload %S" t))v.variant_cases)

let native_parametric_variant_ml params v =
  let head=match params with [p]->p|_->"("^String.concat ", "params^")"in
  let ordinary=native_variant_ml v in
  let prefix="type t ="in
  let offset=String.index ordinary '\n'+1 in
  assert(String.sub ordinary offset(String.length prefix)=prefix);
  String.sub ordinary 0 offset ^ "type " ^head^" t =" ^
  String.sub ordinary (offset+String.length prefix)(String.length ordinary-offset-String.length prefix)
let native_parametric_variant_identity params v =
  "native-parametric-polyvariant\n"^String.concat " "params^"\n"^native_variant_identity v

let native_open_variant_ml row v =
  "(* Generated by Soma: open native polymorphic variant " ^ v.variant_namespace ^ "." ^ v.variant_name ^ ". *)\n" ^
  "type " ^row^" t = ([> " ^ String.concat " | " (List.map(fun c -> "`" ^ c.case_tag ^
    (match c.case_payload with None->""|Some t->" of ("^t^")"))v.variant_cases) ^ " ] as "^row^")\n"
let native_open_variant_identity row v =
  "native-open-polyvariant\n"^row^"\n"^native_variant_identity v

let native_callable_module c =
  let key=Printf.sprintf "soma-native-callable-module-v1:%d:%s:%d:%s"
    (String.length c.callable_namespace)c.callable_namespace
    (String.length c.callable_name)c.callable_name in
  "Soma_callable_" ^ SomaMerkle.string key
let native_callable_type c = native_callable_module c ^ ".t"
let native_callable_filename c = String.uncapitalize_ascii(native_callable_module c)^".ml"
let native_callable_ml c =
  let argument typ = function
    | None->"("^typ^")"
    | Some label when String.starts_with ~prefix:"?" label->
      let suffix=" option"in
      let payload=String.sub typ 0 (String.length typ-String.length suffix)in
      label^":("^payload^")"
    | Some label->label^":("^typ^")"in
  let args=List.map2 argument c.callable_arguments c.callable_labels in
  "(* Generated by Soma: native callable "^c.callable_namespace^"."^c.callable_name^". *)\n"^
  "type t = " ^ String.concat " -> " (args@["("^c.callable_result^")"]) ^ "\n"
let native_callable_identity c =
  String.concat "\n" (["native-callable-type";c.callable_namespace;c.callable_name;native_callable_type c;c.callable_result] @
    List.map2(fun typ label->Printf.sprintf "%S %S" typ(Option.default "" label))c.callable_arguments c.callable_labels)

let native_parametric_callable_ml params c =
  let head=match params with [p]->p|_->"("^String.concat ", "params^")"in
  let ordinary=native_callable_ml c in
  let prefix="type t ="in
  let offset=String.index ordinary '\n'+1 in
  assert(String.sub ordinary offset(String.length prefix)=prefix);
  String.sub ordinary 0 offset ^ "type " ^head^" t =" ^
  String.sub ordinary (offset+String.length prefix)(String.length ordinary-offset-String.length prefix)
let native_parametric_callable_identity params c =
  "native-parametric-callable\n"^String.concat " "params^"\n"^native_callable_identity c

let native_algebraic_module group =
  let namespace = group.algebraic_namespace and name = group.algebraic_name in
  let key = Printf.sprintf "soma-native-algebraic-v1:%d:%s:%d:%s"
    (String.length namespace) namespace (String.length name) name in
  "Soma_algebraic_" ^ SomaMerkle.string key

let native_algebraic_filename group =
  String.uncapitalize_ascii (native_algebraic_module group) ^ ".ml"

let native_algebraic_type group member = native_algebraic_module group ^ "." ^ member

let native_algebraic_declarations ?target ?(exceptions=true) group =
  let record fields =
    let field f =
      (if f.field_mutable then "mutable " else "") ^ f.field_name ^ " : " ^ f.field_type in
    "{ " ^ String.concat "; " (List.map field fields) ^ " }" in
  let payload = function
    | Constructor_arguments [] -> ""
    | Constructor_arguments arguments ->
      " of " ^ String.concat " * " (List.map (fun typ -> "(" ^ typ ^ ")") arguments)
    | Constructor_record fields -> " of " ^ record fields in
  let body = function
    | Algebraic_record fields -> record fields
    | Algebraic_variant constructors ->
      "\n" ^ String.concat "\n" (List.map (fun (name,args) -> "  | " ^ name ^ payload args) constructors) in
  let member (name, data) =
    let prefix=match target with
      |None->name^" = "
      |Some path->name^" = "^path^"."^name^" ="^
        (match data with Algebraic_variant _->""|Algebraic_record _->" ")in
    prefix ^ body data in
  "type " ^
  String.concat "\nand " (List.map member group.algebraic_members) ^ "\n" ^
  (if exceptions then String.concat "" (List.map (fun (name,args) -> "exception " ^ name ^ payload args ^ "\n")
    group.algebraic_exceptions) else "")

let native_algebraic_ml group =
  "(* Generated by Soma: native algebraic types " ^ group.algebraic_namespace ^ "." ^
  group.algebraic_name ^ ". *)\n" ^ native_algebraic_declarations group

let native_algebraic_reexport_ml ?(interface=false) info =
  let equations target = "type "^String.concat "\nand "
    (List.map(fun(name,_)->name^" = "^target^"."^name)info.reexport_group.algebraic_members)^"\n"in
  (* Structural similarity is insufficient: require the target's actual types
     to be the owned schema types. The empty signature exports no helpers. *)
  let witness="((struct\n"^equations info.reexport_target^"end : sig\n"^
    equations(native_algebraic_module info.reexport_group)^"end) : sig end)"in
  (if interface then "include module type of " else "include ")^witness^"\n"^
  native_algebraic_declarations ~target:info.reexport_target ~exceptions:false info.reexport_group

let native_source_type_names info = match info.source_type_body with
  |Source_group group->List.map fst group.algebraic_members
  |_->[info.source_type_name]

let native_source_type_reexport_ml info =
  match info.source_type_body with
  |Source_group group->native_algebraic_declarations ~target:info.source_type_target ~exceptions:false group
  |_->
  let params=match info.source_type_parameters with []->""|[p]->p^" "
    |ps->"("^String.concat ", "ps^") "in
  "type "^params^info.source_type_name^" = "^
  (match info.source_type_body with
   |Source_group _->assert false
   |Source_alias typ->typ^"\n"
   |Source_record fields->params^info.source_type_target^" = { "^
      String.concat "; "(List.map(fun f->(if f.field_mutable then "mutable "else "")^f.field_name^" : "^f.field_type)fields)^" }\n"
   |Source_variant []->params^info.source_type_target^" = |\n"
   |Source_variant cases->params^info.source_type_target^" =\n"^
      String.concat "\n"(List.map(fun(name,fields)->"| "^name^
        (if fields=[]then ""else " of "^String.concat " * "(List.map(fun t->"("^t^")")fields)))cases)^"\n")

let native_source_type_identity info =
  String.concat "\n" ["native-source-type-reexport-v1";info.source_type_namespace;
    info.source_type_source;info.source_type_symbol;string_of_int info.source_type_order;
    native_source_type_reexport_ml info]

let rec native_identity = function
 | OCamlNativeSourceTypeReexport info -> native_source_type_identity info
 | OCamlNativeValueReexport info ->
   String.concat "\n" ["native-value-reexport";info.value_namespace;info.value_name;
     info.value_owner;info.value_module;string_of_int info.value_order;native_identity(OCamlNativeCallback info.value_callback)]
 | OCamlNativeAlgebraicReexport info ->
   String.concat "\n" ["native-algebraic-reexport";info.reexport_namespace;
     info.reexport_name;info.reexport_owner;info.reexport_target;string_of_int info.reexport_order;
     native_algebraic_ml info.reexport_group]
 | OCamlNativeModuleInclude info ->
   String.concat "\n" ["native-module-include";info.module_alias_namespace;
     info.module_alias_name;info.module_alias_target;string_of_int info.module_alias_order]
 | OCamlNativeModuleAlias alias ->
   String.concat "\n" ["native-module-alias";alias.module_alias_namespace;
     alias.module_alias_name;alias.module_alias_target;string_of_int alias.module_alias_order]
 | OCamlNativeAlgebraic (group, member) ->
   "native-algebraic " ^ Printf.sprintf "%S %S" member (native_algebraic_ml group)
 | OCamlNativeOwnedRecord r ->
   String.concat "\n" (["native-owned-record";r.record_namespace;r.record_name;native_record_type r] @
     List.map(fun f->Printf.sprintf "%S %S %s" f.field_name f.field_type
       (if f.field_mutable then "mutable" else "immutable"))r.record_fields)
 | OCamlNativeImmutableRecord(r,info) ->
   String.concat "\n" (["native-immutable-record";r.record_namespace;r.record_name;
    native_record_type r;info.logical_type;info.logical_constructor] @ info.logical_projections @ info.logical_definitions @
    List.map(fun f->Printf.sprintf "%S %S" f.field_name f.field_type)r.record_fields)
 | OCamlNativeOwnedVariant v -> native_variant_identity v
 | OCamlNativeParametricVariant(params,v) -> native_parametric_variant_identity params v
 | OCamlNativeOpenVariant(row,v) -> native_open_variant_identity row v
 | OCamlNativeCallableType c -> native_callable_identity c
 | OCamlNativeParametricCallable(params,c) -> native_parametric_callable_identity params c
 | OCamlNativeType path -> "native-type " ^ Printf.sprintf "%S" path
 | OCamlNativeExternalFamily (params, path) ->
   Printf.sprintf "native-external-family %S %s" path (String.concat " " params)
 | OCamlNativeCallback n ->
   let rec describe_operation = function
    | NativeStaticInvocation(_,Some(term,labels)) ->
      let rec describe = function
        | NativeStaticArgument index -> "argument "^string_of_int index
        | NativeStaticValue operation -> "value ("^describe_operation operation^")"
        | NativeStaticLambda(body,signature) ->
          "lambda ["^native_callable_identity signature^"] ("^describe body^")"
        | NativeStaticCall(operation,values,labels) ->
          "invoke ("^describe_operation operation^") ["^String.concat ";"(List.map describe values)^"] labels ["^
          String.concat ";"(List.map(fun label->Printf.sprintf "%S"(Option.default ""label))labels)^"]" in
      "static-invocation "^describe term^" public ["^
      String.concat ";"(List.map(fun label->Printf.sprintf "%S"(Option.default ""label))labels)^"]"
    | NativeStaticInvocation(_,None) -> invalid_arg "unvalidated static invocation"
    | NativeStaticApplication(target,bound,Some(operation,values,target_labels,labels)) ->
      String.concat "\n" (["static-application "^target^" with "^String.concat " "bound;
        describe_operation operation] @ List.map describe_operation values @
        [String.concat ";"(List.map(fun labels->String.concat " "(List.map(fun label->Printf.sprintf "%S"(Option.default ""label))labels))[target_labels;labels])])
    | NativeStaticApplication(_,_,None)->invalid_arg "unvalidated static application"
    | NativeVariantFunction(tag,Some variant) ->
      "variant-function " ^ Printf.sprintf "%S " tag ^ native_variant_identity variant
    | NativeVariantFunction(_,None)->invalid_arg "unvalidated native variant function"
    | NativeStaticCompositionScope(outer,inner,Some(left,right,outer_labels,inner_labels,labels)) ->
      String.concat "\n" ["static-composition-scope "^outer^" "^inner;
        describe_operation left;describe_operation right;
        String.concat ";"(List.map(fun labels->String.concat " "(List.map(fun label->Printf.sprintf "%S"(Option.default ""label))labels))[outer_labels;inner_labels;labels])]
    | NativeStaticCompositionScope(_,_,None)->invalid_arg "unvalidated static composition scope"
    | NativeStaticFunction(prefix,outer,inner,Some(left,right,outer_labels,inner_labels,labels)) ->
      String.concat "\n" ["static-function " ^ string_of_bool prefix ^ " " ^ outer ^ " " ^ inner;
        describe_operation left;describe_operation right;
        String.concat ";" (List.map(fun labels->String.concat " " (List.map(fun label->Printf.sprintf "%S"(Option.default ""label))labels))[outer_labels;inner_labels;labels])]
    | NativeStaticFunction(_,_,_,None) -> invalid_arg "unvalidated static function"
    | NativeExternalThunkFactory(path,literal) ->
      Printf.sprintf "external-thunk-factory %S %S" path literal
    | NativeVariantFactory(tag,Some variant) ->
      "variant-factory " ^ Printf.sprintf "%S " tag ^ native_variant_identity variant
    | NativeVariantFactory(_,None) -> invalid_arg "unvalidated native variant factory"
    | NativeAssertionFunction(line,column) ->
      Printf.sprintf "assertion-function line %d column %d" line column
    | NativeAssertionFunctionFactory(line,column) ->
      Printf.sprintf "assertion-function-factory line %d column %d" line column
    | NativeAssertionFactory(line,column) ->
      Printf.sprintf "assertion-factory line %d column %d" line column
    | NativeFloatConstant literal -> "float-constant " ^ literal
    | NativeExternalInsertedLiteralFunction(path,literal,after,arity) ->
      Printf.sprintf "external-inserted-literal-function %S %S after %d arity %d" path literal after arity
    | NativeExternalFieldsFunction(path,fields,owner,arity) ->
      Printf.sprintf "external-fields-function %S for %s arity %d reading %s" path owner arity (String.concat " " (List.map(Printf.sprintf "%S")fields))
    | NativeExternalLiteralFunction(path,literal,arity) ->
      Printf.sprintf "external-literal-function %S %S arity %d" path literal arity
    | NativeValue p->"call "^Printf.sprintf "%S" p
    | NativeExternalValue p->"external-call "^Printf.sprintf "%S" p
    | NativePrimitive (byte, native, noalloc) ->
      Printf.sprintf "external-primitive %S native=%s noalloc=%b" byte
        (match native with None -> "same" | Some symbol -> Printf.sprintf "%S" symbol) noalloc
    | NativeExternalConstant p->"external-value "^Printf.sprintf "%S" p
    | NativeExternalLiteralConstant (path, literal)->Printf.sprintf "external-literal-value %S %S" path literal
    | NativeExternalLiteralCallback (path, literal, after)->
      Printf.sprintf "external-literal-call %S %S after %d" path literal after
    | NativeExternalComposedValue (outer, inner, after, arity)->
      Printf.sprintf "external-composed-value %S %S after %d arity %d" outer inner after arity
    | NativeExternalTransformedComposition (outer, inner, after, arity, transform, position) ->
      Printf.sprintf "external-composed-value %S %S after %d arity %d transforming %S at %d"
        outer inner after arity transform position
    | NativeExternalException p->"external-exception "^Printf.sprintf "%S" p
    | NativeConstructorTag(p,n)->Printf.sprintf "constructor-tag %S %d" p n
    | NativeConstructorCase(p,n)->Printf.sprintf "constructor-case %S %d" p n
    | NativeConstructorBuild(p,n)->Printf.sprintf "constructor-build %S %d" p n
    | NativeInlineGet (p,f) -> Printf.sprintf "inline-get %S %S" p f
    | NativeInlineSet (p,f) -> Printf.sprintf "inline-set %S %S" p f
    | NativeInlineBuild (p,fields) ->
      "inline-build " ^ String.concat " " (List.map (Printf.sprintf "%S") (p :: fields))
    | NativeBoundBooleanFunction (path, callable, label, value) ->
      "bound-boolean-function " ^ Printf.sprintf "%S" path ^ " " ^
      native_callable_identity callable ^ " at " ^ Printf.sprintf "%S" label ^
      " = " ^ string_of_bool value
    | NativeDefaultedFunction (path, callable) ->
      "defaulted-function " ^ Printf.sprintf "%S" path ^ " " ^ native_callable_identity callable
    | NativeEtaFunction (path, callable) ->
      "eta-function " ^ Printf.sprintf "%S" path ^ " " ^ native_callable_identity callable
    | NativeDeferredFields (fields, owner) ->
      "deferred-fields " ^ String.concat " " (List.map(Printf.sprintf "%S")fields) ^ " for " ^ owner
    | NativeGetFunction (field, owner) -> Printf.sprintf "get-function %S for %s" field owner
    | NativeSetFunction (field, owner) -> Printf.sprintf "set-function %S for %s" field owner
    | NativeGet p->"get "^Printf.sprintf "%S" p
    | NativeSet p->"set "^Printf.sprintf "%S" p
    | NativeBuild fs->"build "^String.concat " "(List.map(Printf.sprintf "%S")fs)
    | NativeBuildEvaluating (fields, evaluated) ->
      let names fields = String.concat " " (List.map (Printf.sprintf "%S") fields) in
      "build-evaluating " ^ names fields ^ " evaluating " ^ names evaluated
    | NativeRecordFactory (fields, reading, owner) ->
      let names fields = String.concat " " (List.map (Printf.sprintf "%S") fields) in
      "record-factory " ^ names fields ^ " reading " ^ names reading ^ " for " ^ owner
    | NativeVariantDispatch (cases, owner, with_context) ->
      let describe (constructor, pattern, keep_receiver) =
        let payload = match pattern with
          | Dispatch_arguments arity -> Printf.sprintf "arguments %d" arity
          | Dispatch_fields names -> "fields [" ^
            String.concat "; " (List.map (Printf.sprintf "%S") names) ^ "]"
          | Dispatch_ignore with_payload -> Printf.sprintf "ignore %b" with_payload in
        Printf.sprintf "%S %s keep_receiver=%b" constructor payload keep_receiver in
      let context = if with_context then " with context" else "" in
      "variant-dispatch " ^ owner ^ context ^ " [" ^ String.concat "; " (List.map describe cases) ^ "]"
    | NativeCopy fs->"copy "^String.concat " "(List.map(Printf.sprintf "%S")fs)
    | NativeCallableApply(Some c)->"apply "^native_callable_identity c
    | NativeCallableApplyFunction(Some c)->"apply-function "^native_callable_identity c
    | NativeCallableWrap(Some c)->"wrap "^native_callable_identity c
    | NativeCallableWrapFull (Some c) -> "wrap-full " ^ native_callable_identity c
    | NativeCallableApplyFunction None | NativeCallableApply None | NativeCallableWrap None | NativeCallableWrapFull None -> invalid_arg "unvalidated native callable descriptor"
    | NativeVariantView(Some v)->"variant-view "^native_variant_identity v
    | NativeVariantBuild(tag,Some v)->"variant-build "^Printf.sprintf "%S" tag^" "^native_variant_identity v
    | NativeVariantView None | NativeVariantBuild(_,None)->invalid_arg "unvalidated native variant descriptor" in
   let operation=describe_operation n.operation in
   String.concat "\n" (["native-callback";n.namespace;n.name;operation;n.result] @
    List.map2(fun t l->Printf.sprintf "%S %S" t (Option.default "" l))n.arguments n.labels)
 | _ -> invalid_arg "not a native declaration"


(** A checked logical enumeration may share an existing native variant. *)
type native_enum_alias = {
  enum_constant : Names.Constant.t;
  enum_logical_type : string;
  enum_target : string;
  enum_constructors : string list;
  enum_source : string;
}
let native_enum_aliases : (unit -> native_enum_alias list) ref = ref (fun () -> [])

(** Constructor payload representations for a reused checked native variant.
    Kept separate so existing enum metadata and serialized descriptors retain
    their exact shape. No conversion function or logical evaluator is added. *)
type native_variant_alias = {
  variant_alias_constant : Names.Constant.t;
  variant_alias_arguments : string list list;
}
let native_variant_aliases : (unit -> native_variant_alias list) ref = ref (fun () -> [])

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
let native_record_aliases : (unit -> native_record_alias list) ref = ref (fun () -> [])

(** Source-owned native module assembly. Patterns contain identifiers and
    structural destructuring only, never an arbitrary OCaml expression. *)
type native_export_pattern =
  | Export_name of string
  | Export_tuple of native_export_pattern list
  | Export_record of string * string list

type native_assembly = {
  assembly_owner : Names.Constant.t;
  assembly_namespace : string;
  assembly_source : string;
  assembly_value : string;
  assembly_pattern : native_export_pattern;
  assembly_pattern_text : string;
}

let native_assemblies : (unit -> native_assembly list) ref = ref (fun () -> [])

let rec native_export_identity = function
  | Export_name name -> "name " ^ Printf.sprintf "%S" name
  | Export_tuple fields -> "tuple [" ^ String.concat ";" (List.map native_export_identity fields) ^ "]"
  | Export_record (owner, fields) -> "record " ^ Printf.sprintf "%S" owner ^ " [" ^
      String.concat ";" (List.map (Printf.sprintf "%S") fields) ^ "]"

let native_assembly_identity info =
  String.concat "\n" ["native-local-assembly-v1"; info.assembly_namespace;
    info.assembly_value; native_export_identity info.assembly_pattern]

(* Additional scope metadata leaves existing assembly objects unchanged. *)
type native_static_exception = {
  static_exception_name : string;
  static_exception_symbol : string;
  static_exception_arguments : string list;
}
type native_static_exception_scope = {
  static_exception_owner : Names.Constant.t;
  static_exception_fields : native_static_exception list;
}
let native_static_exception_scopes : (unit -> native_static_exception_scope list) ref = ref(fun()->[])
let static_exceptions owner =
  List.concat_map(fun info->if Names.Constant.CanOrd.equal info.static_exception_owner owner
    then info.static_exception_fields else [])(!native_static_exception_scopes())

type native_static_export_kind = Static_value | Static_type of int | Static_unpack
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
let native_static_assemblies : (unit -> native_static_assembly list) ref = ref(fun()->[])
type native_lexical_scope = {
  lexical_owner : Names.Constant.t;
  lexical_opens : string list;
  lexical_functor : (string * (string * string) list) option;
}
let native_lexical_scopes : (unit -> native_lexical_scope list) ref = ref(fun()->[])
let lexical_scope owner = List.find_opt(fun info->Names.Constant.CanOrd.equal info.lexical_owner owner)
  (!native_lexical_scopes())
let native_lexical_scope_identity scope =
  String.concat "\n" (["native-lexical-scope-v1";"capture-owned-callables"] @
    List.map(fun path->"open "^path)scope.lexical_opens @
    (match scope.lexical_functor with None->[]|Some(name,parameters)->
      ("functor "^name)::List.map(fun(name,signature)->name^" : "^signature)parameters))
let native_static_assembly_identity info =
  String.concat "\n" (["native-static-assembly-v1";info.static_namespace;info.static_module] @
    List.map(fun item->
      let kind=match item.static_export_kind with Static_value->"value"
        |Static_type arity->"type "^string_of_int arity|Static_unpack->"module"in
      String.concat " "[kind;Printf.sprintf "%S"item.static_export_name;item.static_export_symbol])info.static_exports) ^
  (match static_exceptions info.static_owner with []->""|exceptions->
    "\nstatic-exceptions-v1\n"^String.concat "\n"(List.map(fun item->
      String.concat " "([Printf.sprintf "%S" item.static_exception_name;item.static_exception_symbol]@
        List.map(Printf.sprintf "%S")item.static_exception_arguments))exceptions)) ^
  (match lexical_scope info.static_owner with None->""|Some scope->"\n"^native_lexical_scope_identity scope)

(* Filled by the OCaml project producer, then by extraction's actual name
   allocator. Consumers never guess collision suffixes or parse OCaml text. *)
let native_static_extraction_requests : (Names.GlobRef.t * bool) list ref = ref []
let native_static_extracted_names : (Names.GlobRef.t * bool * string * int) list ref = ref []
let native_public_extracted_values : string list option ref = ref None

(* Separate metadata keeps existing public-application objects compatible. *)
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
let native_public_types : (unit -> native_public_types list) ref = ref(fun()->[])
let native_public_extracted_types : string list option ref = ref None
let native_public_type_declarations : (Names.GlobRef.t * string * string) list ref = ref []
let public_type_equations owner =
  List.concat_map(fun info->if Names.Constant.CanOrd.equal owner info.types_owner
    then info.types_equations else [])(!native_public_types())

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
let native_public_assemblies : (unit -> native_public_assembly list) ref = ref(fun()->[])
let native_public_assembly_identity info =
  String.concat "\n" (["native-public-assembly-v1";info.public_namespace] @
    List.map(fun item->String.concat " "
      ([Printf.sprintf "%S"item.application_name;Printf.sprintf "%S"item.application_signature]@
       item.application_symbols))info.public_applications) ^
  (match public_type_equations info.public_owner with []->""|equations->
    "\npublic-type-equations-v1\n"^String.concat "\n"(List.map(fun item->
      Printf.sprintf "%S %s %d" item.equation_name item.equation_symbol item.equation_arity)equations))
