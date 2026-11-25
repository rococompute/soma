(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: OCaml modules (theories/Soma/OCaml.v).

   FILE.definition declares, [name : type.], what Soma takes the values
   and types of FILE.ml to be: each is a parameter (vernac/g_vernac.mlg),
   which [OCaml Bind], at the end of the file, ties to FILE.ml's value or
   type of that name, in the submodule of its Soma module, once it has
   found the OCaml type that the declared type is. Next to no module,
   FILE.definition declares a library's module, File ([OCaml Bind
   Module]). A named argument ([forall (attrs : ...), ...]) is OCaml's
   labeled one. [OCaml Library "lib".] names a findlib library that the
   module is, or uses. The bindings are kept with the library, and known
   wherever it is loaded.

   Soma never computes them: to the kernel and to the evaluation of a term
   they are parameters. A program whose main uses them is built with them
   by OCaml (toplevel/somaOcaml.ml), which checks each declaration. *)

open Names
open Pp

type binding = {
  key : string;             (* FILE.ml relative to the project, absolute for a dependency, or a library name *)
  top : string;             (* its name in OCaml: Web, Async *)
  path : string;            (* the declaration's in it: vtext, Deferred.bind *)
  item : SomaForeign.ocaml_item;
}

let bindings = Summary.ref ~name:"soma-ocaml-bindings" Cmap_env.empty

let in_binding : Constant.t * binding -> Libobject.obj =
  Libobject.declare_object @@ Libobject.superglobal_object_nodischarge "Soma OCaml binding"
    ~cache:(fun (c, b) -> bindings := Cmap_env.add c b !bindings)
    ~subst:None

(* Reusing an enum records its existing checked inductive and generates only
   typed native references and an exhaustive ABI check, never conversion code. *)
let native_enums = Summary.ref ~name:"soma-native-enum-aliases" []
let in_native_enum =
  Libobject.declare_object @@ Libobject.superglobal_object_nodischarge "Soma native enum alias"
    ~cache:(fun info -> native_enums := info :: !native_enums)
    ~subst:None
let () = SomaForeign.native_enum_aliases := (fun () -> !native_enums)
let native_variant_aliases = Summary.ref ~name:"soma-native-variant-aliases" []
let in_native_variant_alias =
  Libobject.declare_object @@ Libobject.superglobal_object_nodischarge "Soma native variant alias"
    ~cache:(fun info -> native_variant_aliases := info :: !native_variant_aliases)
    ~subst:None
let () = SomaForeign.native_variant_aliases := (fun () -> !native_variant_aliases)
let native_record_aliases = Summary.ref ~name:"soma-native-record-aliases" []
let in_native_record_alias =
  Libobject.declare_object @@ Libobject.superglobal_object_nodischarge "Soma native record alias"
    ~cache:(fun info -> native_record_aliases := info :: !native_record_aliases)
    ~subst:None
let () = SomaForeign.native_record_aliases := (fun () -> !native_record_aliases)



(* the modules, by key: FILE.ml or none, their name, and the libraries
   they use *)
let modules = Summary.ref ~name:"soma-ocaml-modules" CString.Map.empty

let in_module : string * (string option * string * string list) -> Libobject.obj =
  Libobject.declare_object @@ Libobject.superglobal_object_nodischarge "Soma OCaml module"
    ~cache:(fun (key, m) -> modules := CString.Map.add key m !modules)
    ~subst:None

(* * OCaml Library *)

(* the libraries named by the file being compiled, until [OCaml Bind] *)
let pending = Summary.ref ~name:"soma-ocaml-libraries" []

let is_library_name s =
  s <> "" && String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '.' | '-' -> true | _ -> false) s

let library libraries =
  List.iter (fun l ->
      if not (is_library_name l) then
        CErrors.user_err (str "OCaml Library: " ++ qstring l ++ str " is not the name of a findlib library" ++
                          str " (as dune's (libraries ...) has them: bonsai.web, lwt.unix)."))
    libraries;
  pending := !pending @ List.filter (fun l -> not (List.mem l !pending)) libraries

(* * OCaml Bind *)

let is_module_name base =
  base <> "" &&
  (match base.[0] with 'a'..'z' | 'A'..'Z' -> true | _ -> false) &&
  String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true | _ -> false) base

(* FILE.ml, and FILE.definition next to no module, are the OCaml module File *)
let module_name file =
  let base = Filename.remove_extension (Filename.basename file) in
  if not (is_module_name base) then
    CErrors.user_err (str (Filename.basename file) ++ str " is not the name of an OCaml module:" ++ spc () ++
                      str "it starts with a letter, followed by letters, digits, _ and '.");
  String.capitalize_ascii base

let keywords = [
  "and"; "as"; "assert"; "begin"; "class"; "constraint"; "do"; "done"; "downto"; "else"; "end";
  "exception"; "external"; "false"; "for"; "fun"; "function"; "functor"; "if"; "in"; "include";
  "inherit"; "initializer"; "lazy"; "let"; "match"; "method"; "module"; "mutable"; "new"; "nonrec";
  "object"; "of"; "open"; "or"; "private"; "rec"; "sig"; "struct"; "then"; "to"; "true"; "try";
  "type"; "val"; "virtual"; "when"; "while"; "with" ]

(* a value or type of OCaml is named in lowercase *)
let ocaml_name ~definition name =
  let valid = name <> "" && (match name.[0] with 'a'..'z' | '_' -> true | _ -> false) &&
              not (List.mem name keywords) in
  if not valid then
    CErrors.user_err (str definition ++ str " declares " ++ str name ++ str "," ++ spc () ++
                      str "which OCaml cannot name: OCaml's values and types start with a lowercase letter," ++
                      spc () ++ str "and are no keyword.");
  name

exception Not_ocaml of Pp.t

let not_ocaml msg = raise (Not_ocaml msg)

let ref_of name = if Rocqlib.has_ref name then Some (Rocqlib.lib_ref name) else None

(* the parameters of a type variable's name: [A] is ['a] *)
let type_variable used na =
  let base = match na with
    | Name id ->
      let s = String.uncapitalize_ascii (Id.to_string id) in
      if String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true | _ -> false) s
         && s <> "" && (match s.[0] with 'a'..'z' -> true | _ -> false) then s else "t"
    | Anonymous -> "t" in
  let rec fresh k =
    let v = "'" ^ (if k = 0 then base else base ^ string_of_int k) in
    if List.mem v used then fresh (k + 1) else v in
  fresh 0

let is_sort env sigma t = EConstr.isSort sigma (Reductionops.whd_all env sigma t)

(* The OCaml type of a declared type: [string], [bool], [nat], [unit], [list],
   [option], products, [float], [word64], functions, types of OCaml modules that a
   .definition declares, and type variables ([forall A, ...]), which
   extraction erases as arguments *)
let rec ocaml_type env sigma vars t =
  let t=Reductionops.whd_betaiotazeta env sigma t in
  let reused_record =
    let head,args = EConstr.decompose_app sigma t in
    match EConstr.kind sigma head with
    | Ind((m,0),_) ->
      let symbol=KerName.to_string(MutInd.canonical m) in
      List.find_map(fun info->
        if info.SomaForeign.record_alias_logical_type<>symbol ||
           List.length info.record_alias_parameters<>Array.length args then None else
        let parameters=Array.to_list(Array.map(ocaml_type env sigma vars)args) in
        let applied=match parameters with []->"" |[p]->"("^p^") "
          |ps->"("^String.concat ", "ps^") " in
        Some(applied^info.record_alias_target))!native_record_aliases
    |_->None in
  let native = match reused_record with Some _ as result->result |None->match EConstr.kind sigma t with
    | Const (c, _) -> (match Cmap_env.find_opt c !bindings with
      | Some { item = SomaForeign.OCamlNativeType path; _ } -> Some path
      | Some { item = SomaForeign.OCamlNativeAlgebraic (group, member); _ } ->
        Some (SomaForeign.native_algebraic_type group member)
      | Some { item = (SomaForeign.OCamlNativeOwnedRecord r | SomaForeign.OCamlNativeImmutableRecord(r,_)); _ } -> Some(SomaForeign.native_record_type r)
      | Some { item = SomaForeign.OCamlNativeOwnedVariant v; _ } -> Some(SomaForeign.native_variant_type v)
      | Some { item = SomaForeign.OCamlNativeCallableType c; _ } -> Some(SomaForeign.native_callable_type c)
      | _ -> None)
    | App(head,args) -> (match EConstr.kind sigma head with
      |Const(c,_)->(match Cmap_env.find_opt c !bindings with
        | Some {item=SomaForeign.OCamlNativeExternalFamily (params, path); _}
          when List.length params = Array.length args ->
          let args = Array.to_list (Array.map (ocaml_type env sigma vars) args) in
          Some ("(" ^ String.concat ", " args ^ ") " ^ path)
        |Some{item=SomaForeign.OCamlNativeParametricCallable(params,c);_} when List.length params=Array.length args ->
          let args=Array.to_list(Array.map(ocaml_type env sigma vars)args)in
          let applied=match args with [arg]->"("^arg^")"|_->"("^String.concat ", "args^")"in
          Some(applied^" "^SomaForeign.native_callable_type c)
        |Some{item=SomaForeign.OCamlNativeOpenVariant(_,v);_} when Array.length args=1 ->
          Some("("^ocaml_type env sigma vars args.(0)^") "^SomaForeign.native_variant_type v)
        |Some{item=SomaForeign.OCamlNativeParametricVariant(params,v);_} when List.length params=Array.length args ->
          let args=Array.to_list(Array.map(ocaml_type env sigma vars)args)in
          let applied=match args with [arg]->"("^arg^")"|_->"("^String.concat ", "args^")"in
          Some(applied^" "^SomaForeign.native_variant_type v)
        |_->None)
      |_->None)
    | Ind((m,0),_) ->
      let symbol=KerName.to_string(MutInd.canonical m)in
      let reused=List.find_opt(fun info->info.SomaForeign.enum_logical_type=symbol)!native_enums in
      (match reused with Some info->Some info.SomaForeign.enum_target | None->
      Cmap_env.fold(fun _ binding found->match found,binding.item with
       |None,SomaForeign.OCamlNativeImmutableRecord(r,info)when info.logical_type=symbol->Some(SomaForeign.native_record_type r)
       |_->found)!bindings None)
    | _ -> None in
  match native with Some path -> path | None ->
  (* Unfold an ordinary type alias one constant at a time. Full reduction can
     otherwise pass through its registered native type and lose that ABI. *)
  let head,_=EConstr.decompose_app sigma t in
  let alias=match EConstr.kind sigma head with
    |Const(c,_)when not(Cmap_env.mem c !bindings)->
      let unfolded=Reductionops.whd_const c env sigma t in
      if EConstr.eq_constr sigma t unfolded then None else Some unfolded
    |_->None in
  match alias with Some typ->ocaml_type env sigma vars typ |None->
  let t = Reductionops.whd_all env sigma t in
  match EConstr.kind sigma t with
  | Prod (na, dom, cod) ->
    let env' = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, dom)) env in
    if is_sort env sigma dom then
      let v = type_variable (List.filter_map Fun.id vars) na.Context.binder_name in
      ocaml_type env' sigma (Some v :: vars) cod
    else if not (EConstr.Vars.noccurn sigma 1 cod) then
      not_ocaml (str "its result depends on an argument, which OCaml's types cannot say")
    else
      let d = ocaml_type env sigma vars dom in
      let d = if EConstr.isProd sigma (Reductionops.whd_all env sigma dom) then "(" ^ d ^ ")" else d in
      d ^ " -> " ^ ocaml_type env' sigma (None :: vars) cod
  | Rel n ->
    (match List.nth_opt vars (n - 1) with
     | Some (Some v) -> v
     | _ -> not_ocaml (str "it uses a value as a type"))
  | _ ->
    let f, args = EConstr.decompose_app sigma t in
    let args = Array.to_list args in
    let is name = match ref_of name with Some gr -> EConstr.isRefX env sigma gr f | None -> false in
    (* a function, as an argument of a type, is in parentheses *)
    let arg a =
      let s = ocaml_type env sigma vars a in
      if EConstr.isProd sigma (Reductionops.whd_all env sigma a) then "(" ^ s ^ ")" else s in
    if GradualTyping.is_unknown_type env sigma t then
      not_ocaml (str "Any has no OCaml type: an OCaml value has one type")
    (* Executable result boundaries erase to their result, just as in native
       extraction. This lets typed native callable wrappers label a checked
       entry/group-producing function. It adds no logical evaluator: values
       still cannot be run or inspected by a logical consumer. *)
    else if List.exists is ["soma.native.entry"; "soma.native.callback_group";
                            "soma.native.function_group"; "soma.native.function_knot"; "soma.native.preparation"] then
      (match args with [result]->ocaml_type env sigma vars result
       |_->not_ocaml(str "a native result boundary needs one result type"))
    else if is "core.string.type" then "string"
    else if is "core.ascii.type" then "char"
    else if is "core.bool.type" then "bool"
    else if is "core.unit.type" then "unit"
    else if is "num.float.type" then "float"
    (* nat as extraction has it, OCaml's int: Soma_nat.nat, which
       toplevel/somaOcaml.ml generates *)
    else if is "num.nat.type" then "Soma_nat.nat"
    (* Rocq's primitive 63-bit integer, as extraction has it: OCaml's
       int, Uint63.t of the generated uint63.ml *)
    else if is "num.int63.type" then "Uint63.t"
    (* Soma.Word64's unsigned 64-bit words: OCaml's int64, read unsigned
       (soma_word64.ml) *)
    else if is "soma.word64.type" then "Soma_word64.t"
    (* Sandbox's native handles: bytes, references, promises and deferred computations,
       which soma_handles.ml names (toplevel/somaMirage.ml,
       handles_ml): FILE.ml gives an ['a Lwt.t] *)
    else if is "soma.buffer.type" then "Bytes.t"
    else if is "soma.promise.type" then arg (List.hd args) ^ " Soma_handles.promise"
    else if is "soma.deferred.type" then arg (List.hd args) ^ " Soma_handles.deferred"
    else if is "soma.reference.type" then arg (List.hd args) ^ " Soma_handles.reference"
    else if is "soma.exception_value.type" then "Soma_handles.exception_value"
    else if is "soma.native.program" then arg (List.hd args) ^ " Soma_effect.t"
    else if is "soma.native.entry" || is "soma.native.callback_group" || is "soma.native.function_group" then arg (List.hd args) ^ " Soma_effect.entry"
    else if is "soma.native.callback" then
      "(" ^ String.concat ", " (List.map arg args) ^ ") Soma_effect.callback"
    else if is "soma.native.triple" || is "soma.native.quadruple" || is "soma.native.quintuple" then
      "(" ^ String.concat " * " (List.map arg args) ^ ")"
    else if is "soma.native.vector" then arg (List.hd args) ^ " Soma_effect.vector"
    else if is "soma.native.text_buffer" then "Soma_effect.text_buffer"
    else if is "soma.native.table" then
      "(" ^ String.concat ", " (List.map arg args) ^ ") Soma_effect.table"
    else if is "soma.native.result" then
      "(" ^ arg (List.nth args 0) ^ ", " ^ arg (List.nth args 1) ^ ") result"
    else if is "core.list.type" then arg (List.hd args) ^ " list"
    else if is "core.option.type" then arg (List.hd args) ^ " option"
    else if is "core.prod.type" then
      "(" ^ arg (List.nth args 0) ^ " * " ^ arg (List.nth args 1) ^ ")"
    else
      match EConstr.kind sigma f with
      | Const (c, _) ->
        (match Cmap_env.find_opt c !bindings with
         | Some { top; path; item = SomaForeign.OCamlType n; _ } when n = List.length args ->
           let path = top ^ "." ^ path in
           (match args with
            | [] -> path
            | [a] -> arg a ^ " " ^ path
            | args -> "(" ^ String.concat ", " (List.map (ocaml_type env sigma vars) args) ^ ") " ^ path)
         | _ -> not_ocaml (Printer.pr_econstr_env env sigma t ++ str " is no type of OCaml"))
      | _ -> not_ocaml (Printer.pr_econstr_env env sigma t ++ str " is no type of OCaml")

(* [Type -> Type]: a type of OCaml with one parameter *)
let type_arity env sigma t =
  let decls, result = Reductionops.whd_decompose_prod env sigma t in
  if EConstr.isSort sigma result && List.for_all (fun (_, d) -> is_sort env sigma d) decls
  then Some (List.length decls) else None

(* the arguments of a value of type [t], types left out: those it is
   applied to in OCaml, each with its label, a named argument's
   ([forall (attrs : list Attr.t), ...] is [~attrs]), or none ([A -> B]) *)
let rec labels ~definition env sigma t =
  let t = Reductionops.whd_all env sigma t in
  match EConstr.kind sigma t with
  | Prod (na, dom, cod) ->
    let env' = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, dom)) env in
    let rest = labels ~definition env' sigma cod in
    if is_sort env sigma dom then rest
    else
      let label = match na.Context.binder_name with
        | Name id -> Some (ocaml_name ~definition (Id.to_string id))
        | Anonymous -> None in
      label :: rest
  | _ -> []

(* The declarations of the file being compiled, tied to the OCaml module
   [top]: each is the type or value of its name, in the submodule of its
   Soma module ([Module Deferred. bind : ... End Deferred.] is
   [Top.Deferred.bind]). [ml_file] is FILE.ml, or none for a library's
   module. *)
let bind_module ~key ~ml_file ~top ~definition =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let lib = Lib.library_dp () in
  let has = match ml_file with Some f -> Filename.basename f | None -> top in
  (* the submodules a constant is in, from the file down *)
  let rec submodules = function
    | ModPath.MPfile d when DirPath.equal d lib -> Some []
    | ModPath.MPdot (mp, l) ->
      Option.map (fun p ->
          let m = Id.to_string l in
          if not (is_module_name m) || m.[0] <> Char.uppercase_ascii m.[0] then
            CErrors.user_err (str definition ++ str ": " ++ str m ++
                              str " is no name of an OCaml module, which starts with a capital letter.");
          p @ [m]) (submodules mp)
    | _ -> None in
  let constants = Environ.fold_constants (fun c cb acc ->
      match submodules (Constant.modpath c) with
      | Some subs -> (c, subs, cb) :: acc
      | None -> acc) env [] in
  let constants = List.sort (fun (a, _, _) (b, _, _) -> Constant.CanOrd.compare a b) constants in
  let generated_logical c =
    let path=KerName.to_string(Constant.canonical c)in
    Cmap_env.exists(fun _ binding->match binding.item with
     |SomaForeign.OCamlNativeImmutableRecord(_,info)->List.mem path info.logical_definitions
     |_->false)!bindings in
  (* Checked type-only helpers may name existing representations or recover
     a native signature. They supply no runtime implementation for a module:
     leave them in the logical environment, outside the OCaml value bindings. *)
  let type_definition cb = match cb.Declarations.const_body with
    |Declarations.Def _ ->
      let sigma=Evd.from_env env in
      let rec result_is_sort env typ =
        match EConstr.kind sigma(Reductionops.whd_all env sigma typ)with
        |Sort _->true
        |Prod(na,domain,codomain)->
          result_is_sort(EConstr.push_rel(Context.Rel.Declaration.LocalAssum(na,domain))env)codomain
        |_->false in
      result_is_sort env(EConstr.of_constr cb.Declarations.const_type)
    |_->false in
  let constants = List.filter (fun (c, _, cb) ->
    not (Cmap_env.mem c !bindings) && not(generated_logical c) && not(type_definition cb)) constants in
  let constants = List.map (fun (c, subs, cb) ->
      let name = Id.to_string (Constant.label c) in
      (match cb.Declarations.const_body with
       | Declarations.Undef _ -> ()
       | _ -> CErrors.user_err (str definition ++ str " declares what " ++ str has ++
                                str " has, and defines nothing: " ++ str name ++ str " is a definition."));
      let name = ocaml_name ~definition name in
      c, String.concat "." (subs @ [name]), name, EConstr.of_constr cb.Declarations.const_type) constants in
  (* the types first: the values' types may be among them *)
  let types, values = List.partition (fun (_, _, _, t) -> Option.has_some (type_arity env sigma t)) constants in
  List.iter (fun (c, path, _, t) ->
      let n = Option.get (type_arity env sigma t) in
      Lib.add_leaf (in_binding (c, { key; top; path; item = SomaForeign.OCamlType n })))
    types;
  List.iter (fun (c, path, name, t) ->
      let ty = try ocaml_type env sigma [] t
        with Not_ocaml why ->
          CErrors.user_err (hov 0 (str name ++ str " : " ++ Printer.pr_econstr_env env sigma t ++
                                   str " is not given to OCaml:" ++ spc () ++ why ++ str "." ++ spc () ++
                                   str "An OCaml value's type is made of string, bool, nat, unit, list, option," ++ spc () ++
                                   str "products, float, functions, types that " ++ str definition ++ spc () ++
                                   str "declares (name : Type.), and type variables (forall A, ...).")) in
      Lib.add_leaf (in_binding (c, { key; top; path; item = SomaForeign.OCamlValue (ty, labels ~definition env sigma t) })))
    values;
  Lib.add_leaf (in_module (key, (ml_file, top, !pending)))

(* Assumption-free native declarations. Every generated logical constant has
   a body: a canonical named placeholder, never an external evaluator. *)
let native_error message = CErrors.user_err (str "OCaml Native: " ++ str message)
let native_context () =
  let file = match !SomaImport.source_file with
    | Some file when Filename.check_suffix file ".definition" -> file
    | _ -> native_error "declarations belong in a .definition file" in
  let base = Filename.chop_suffix file ".definition" in
  let ml = base ^ ".ml" in
  let top = module_name ml in
  let ml_file = if Sys.file_exists ml then Some (SomaImport.project_file ml) else None in
  let key = Option.default top ml_file in
  key, ml_file, top

let native_path path =
  let parts = String.split_on_char '.' path in
  match List.rev parts with
  | [] -> native_error "an external path is empty"
  | value :: modules ->
    ignore (ocaml_name ~definition:"native declaration" value);
    if not(String.for_all(function 'a'..'z'|'A'..'Z'|'0'..'9'|'_'|'\''->true|_->false)value)
    then native_error "an external path has an invalid value name";
    if List.exists (fun p -> not (is_module_name p) || p.[0] <> Char.uppercase_ascii p.[0]) modules
    then native_error "an external path has an invalid module name";
    path

(* A qualified symbolic reference is a value expression. Keep this grammar
   separate from native type and field paths, which only admit identifiers. *)
let native_external_path path =
  match String.index_opt path '(' with
  | None -> native_path path
  | Some open_paren ->
    let invalid () = native_error "an external operator needs a qualified OCaml operator path" in
    if open_paren < 2 || path.[open_paren - 1] <> '.' ||
       not (String.ends_with ~suffix:")" path)
    then invalid ();
    let qualification = String.sub path 0 (open_paren - 1) in
    let modules = String.split_on_char '.' qualification in
    if not (List.for_all (fun part ->
      is_module_name part && part.[0] = Char.uppercase_ascii part.[0]) modules)
    then invalid ();
    let operator = String.trim
      (String.sub path (open_paren + 1) (String.length path - open_paren - 2)) in
    let symbol c = String.contains "!$%&*+-./:<=>?@^|~" c in
    let valid_head =
      String.length operator > 0 &&
      match operator.[0] with
      | '!' | '$' | '%' | '&' | '*' | '+' | '-' | '/' | '<' | '=' | '>' | '@' | '^' | '|' -> true
      | '~' | '?' -> String.length operator > 1
      | ':' -> String.equal operator ":="
      | _ -> false
    in
    if not (valid_head && String.for_all symbol operator) ||
       List.mem operator ["->"; "<-"; "|"]
    then invalid ();
    (* Spaces prevent an adjacent star from opening an OCaml comment. *)
    qualification ^ ".( " ^ operator ^ " )"

let native_global name =
  CAst.make (Constrexpr.CRef (Libnames.qualid_of_path
    (Nametab.path_of_global (Rocqlib.lib_ref name)), None))
let native_app f args = CAst.make (Constrexpr.CApp (f, List.map (fun a -> a, None) args))
let native_string value =
  let byte c = native_app (native_global "core.ascii.ascii")
    (List.init 8 (fun bit -> native_global
      (if Char.code c land (1 lsl bit) = 0 then "core.bool.false" else "core.bool.true"))) in
  let result = ref (native_global "core.string.empty") in
  for i=String.length value-1 downto 0 do
    result := native_app (native_global "core.string.string") [byte value.[i];!result]
  done;
  !result
let native_declare name body typ =
  ComDefinition.do_definition ~name ~poly:PolyFlags.default ~kind:Decls.Definition
    None [] None body typ;
  match Nametab.locate (Libnames.qualid_of_ident name) with
  | GlobRef.ConstRef c -> c
  | _ -> CErrors.anomaly (str "native declaration is not a constant")
let native_namespace () = ModPath.to_string (Lib.current_mp ())
let native_register name c item =
  let key, ml_file, top = native_context () in
  (* The descriptor symbol, rather than its target, names a generated wrapper. *)
  let path = "__native__." ^ native_namespace () ^ "." ^ Id.to_string name in
  Lib.add_leaf (in_binding (c, {key; top; path; item}));
  Lib.add_leaf (in_module (key, (ml_file, top, !pending)))
(* A module alias is a declaration, not a callable or opaque logical type.
   Its canonical unit token records dependency/ownership without a new axiom. *)
let native_module_alias name target =
  ignore(native_context());
  let valid part=is_module_name part && part.[0]>='A' && part.[0]<='Z' in
  let alias=Id.to_string name in
  if not(valid alias) then native_error "a module alias needs an uppercase OCaml module name";
  if not(List.for_all valid(String.split_on_char '.' target)) then
    native_error "a module alias target needs a qualified OCaml module path";
  let namespace=native_namespace() in
  let order=Cmap_env.fold(fun _ binding count->match binding.item with
    |SomaForeign.OCamlNativeModuleAlias info when info.module_alias_namespace=namespace->count+1
    |_->count)!bindings 0 in
  let source=match !SomaImport.source_file with Some file->SomaImport.project_file file|None->assert false in
  let c=native_declare name (native_global "core.unit.tt") (Some(native_global "core.unit.type"))in
  native_register name c (SomaForeign.OCamlNativeModuleAlias {
    module_alias_namespace=namespace;module_alias_name=alias;module_alias_target=target;
    module_alias_source=source;module_alias_order=order})

let native_external_family name parameters path =
  ignore (native_context ());
  if not (Rocqlib.has_ref "soma.native.family") then native_error "import Soma.Native first";
  let path = native_path path in
  let ids = List.map fst parameters in
  if List.length (List.sort_uniq Id.compare ids) <> List.length ids then
    native_error "native type parameters must be distinct";
  let env = Global.env () in
  let binders = List.map (fun (id, typ) ->
    let sigma, checked = Constrintern.interp_type_evars env (Evd.from_env env) typ in
    (match EConstr.kind sigma checked with
     | Sort sort when not (EConstr.ESorts.is_prop sigma sort || EConstr.ESorts.is_sprop sigma sort) -> ()
     | _ -> native_error "native type parameters must have sort Type or Set");
    Constrexpr.CLocalAssum
      ([CAst.make (Name id)], None, Constrexpr.Default Glob_term.Explicit, typ)) parameters in
  let names = List.rev (List.fold_left (fun used id -> type_variable used (Name id) :: used) [] ids) in
  let symbol = native_string (native_namespace () ^ "." ^ Id.to_string name) in
  let args = List.map (fun id -> CAst.make (Constrexpr.CRef (Libnames.qualid_of_ident id, None))) ids in
  let rec pack = function
    | [] -> assert false
    | [arg] -> arg
    | arg :: rest -> native_app (native_global "core.prod.type") [arg; pack rest] in
  let family = native_app (native_global "soma.native.family") [symbol; pack args] in
  let c = native_declare name (CAst.make (Constrexpr.CLambdaN (binders, family))) None in
  native_register name c (SomaForeign.OCamlNativeExternalFamily (names, path))

let native_type ?(external_=false) name path =
  ignore (native_context ());
  if not (Rocqlib.has_ref "soma.native.handle") then native_error "import Soma.Native first";
  let _, _, top = native_context () in
  let path = if external_ then native_path path else top ^ "." ^ native_path path in
  let symbol = native_namespace () ^ "." ^ Id.to_string name in
  let body = native_app (native_global "soma.native.handle") [native_string symbol] in
  let c = native_declare name body None in
  native_register name c (SomaForeign.OCamlNativeType path)

(* [OCaml Native Enum alias := checked.kind As "Module.kind"]. Reuse the
   logical constructors directly; the emitted type equation validates their
   exact order, arity and completeness even for identity-only native clients. *)
let native_enum ?(variant=false) name source target =
  ignore(native_context());
  let target=native_path target in
  let qualification=String.split_on_char '.' target in
  if List.length qualification<2 then native_error "an enum needs a qualified native type";
  let env=Global.env() in
  let ind=match Nametab.locate source with
    |GlobRef.IndRef ind->ind
    |_->native_error "an enum alias needs an existing inductive type" in
  let mib,mip=Inductive.lookup_mind_specif env ind in
  if Array.length mib.Declarations.mind_packets<>1 || mib.mind_nparams<>0 || mip.mind_nrealargs<>0 ||
     Array.length mip.mind_consnames=0 || (not variant && Array.exists((<>)0)mip.mind_consnrealdecls) ||
     mib.mind_finite=Declarations.CoFinite then
    native_error "an enum alias needs a nonempty, unparameterized, unindexed type with nullary constructors";
  let sigma=Evd.from_env env in
  (match EConstr.kind sigma(EConstr.of_constr mip.mind_user_arity) with
   |Sort sort when not(EConstr.ESorts.is_prop sigma sort || EConstr.ESorts.is_sprop sigma sort)->()
   |_->native_error "a logical proof type cannot be a native enum");
  let payloads = if not variant then None else begin
    let rec fields typ =
      let typ=Reductionops.whd_all env sigma typ in
      match EConstr.kind sigma typ with
      |Prod(_,domain,codomain)->
        if not(EConstr.Vars.noccurn sigma 1 codomain) then
          native_error "native variant payloads cannot depend on previous values";
        let representation=try ocaml_type env sigma [] domain with Not_ocaml why->
          CErrors.user_err(str "OCaml Native variant payload: " ++ why) in
        representation :: fields(EConstr.Vars.subst1 domain codomain)
      |_->[] in
    Some(Array.to_list(Array.map(fun typ->fields(EConstr.of_constr typ))mip.mind_user_lc))
  end in
  let prefix=String.concat "." (List.rev(List.tl(List.rev qualification))) in
  let constructors=Array.to_list(Array.map(fun id->
    let name=Id.to_string id in
    if not(is_module_name name) || name.[0]<>Char.uppercase_ascii name.[0] || name.[0]='_' then
      native_error "native enum constructors need uppercase OCaml names";
    prefix^"."^name)mip.mind_consnames) in
  let logical_type=KerName.to_string(MutInd.canonical(fst ind)) in
  if List.exists(fun info->info.SomaForeign.record_alias_logical_type=logical_type)!native_record_aliases then
    native_error "one logical type cannot mix native record and variant aliases";
  if List.exists(fun info->info.SomaForeign.enum_logical_type=logical_type && info.enum_target<>target)!native_enums then
    native_error "one logical enum cannot use conflicting native types";
  let body=CAst.make(Constrexpr.CRef(source,None)) in
  let c=native_declare name body None in
  native_register name c (SomaForeign.OCamlNativeType target);
  let enum_source=match !SomaImport.source_file with Some f->SomaImport.project_file f|None->assert false in
  Lib.add_leaf(in_native_enum SomaForeign.{enum_constant=c;enum_logical_type=logical_type;
    enum_target=target;enum_constructors=constructors;enum_source});
  Option.iter(fun variant_alias_arguments ->
    Lib.add_leaf(in_native_variant_alias SomaForeign.{variant_alias_constant=c;variant_alias_arguments}))payloads


(* Reuse an existing checked immutable record, including ordinary Type
   parameters. Only the ABI is named: no evaluator, shim or conversion is made. *)
let native_record_alias name source target =
  ignore(native_context());
  let target=native_path target in
  if List.length(String.split_on_char '.' target)<2 then
    native_error "a record alias needs a qualified native type";
  let env=Global.env() in
  let ind=match Nametab.locate source with
    |GlobRef.IndRef ind->ind
    |_->native_error "a record alias needs an existing checked record" in
  let mib,mip=Inductive.lookup_mind_specif env ind in
  if Array.length mib.Declarations.mind_packets<>1 || mip.mind_nrealargs<>0 ||
     Array.length mip.mind_consnames<>1 || mib.mind_finite=Declarations.CoFinite then
    native_error "a native record alias must be a nonrecursive, unindexed record";
  let structure=try Structures.Structure.find env ind with Not_found->
    native_error "a native record alias needs an existing checked record" in
  let sigma=Evd.from_env env in
  let rec parameters count env vars used typ =
    if count=0 then env,vars,List.rev used,typ else
    match EConstr.kind sigma(Reductionops.whd_all env sigma typ)with
    |Prod(na,domain,codomain)->
      (match EConstr.kind sigma(Reductionops.whd_all env sigma domain)with
       |Sort sort when not(EConstr.ESorts.is_prop sigma sort || EConstr.ESorts.is_sprop sigma sort)->()
       |_->native_error "native record parameters must be types");
      let param=type_variable used na.Context.binder_name in
      let env=EConstr.push_rel(Context.Rel.Declaration.LocalAssum(na,domain))env in
      parameters(count-1)env(Some param::vars)(param::used)codomain
    |_->native_error "unsupported checked record parameter shape" in
  let parameter_env,vars,params,arity=parameters mib.mind_nparams env [] []
      (EConstr.of_constr mip.mind_user_arity)in
  (match EConstr.kind sigma(Reductionops.whd_all parameter_env sigma arity)with
   |Sort sort when not(EConstr.ESorts.is_prop sigma sort || EConstr.ESorts.is_sprop sigma sort)->()
   |_->native_error "logical proof records cannot be native records");
  let rec strip count env typ =
    if count=0 then typ else
    match EConstr.kind sigma(Reductionops.whd_all env sigma typ)with
    |Prod(na,domain,codomain)->
      strip(count-1)(EConstr.push_rel(Context.Rel.Declaration.LocalAssum(na,domain))env)codomain
    |_->native_error "unsupported checked record constructor" in
  let typ=strip mib.mind_nparams env(EConstr.of_constr mip.mind_user_lc.(0))in
  let rec fields env vars typ projections = match projections with
    |[]->(match EConstr.kind sigma(Reductionops.whd_all env sigma typ)with
      |Prod _ |LetIn _->native_error "native record fields do not match their projections"
      |_->[])
    |projection::rest->
      if not projection.Structures.Structure.proj_true then
        native_error "defined record fields cannot be native ABI fields";
      let name=match projection.proj_name with Name id->Id.to_string id
        |Anonymous->native_error "native record fields must have names" in
      ignore(ocaml_name ~definition:"native record field" name);
      ignore(native_path name);
      let projection=match projection.proj_body with Some c->
        KerName.to_string(Constant.canonical c)
        |None->native_error "native record fields need ordinary checked projections"in
      match EConstr.kind sigma(Reductionops.whd_all env sigma typ)with
      |Prod(na,domain,codomain)->
        if not(EConstr.Vars.noccurn sigma 1 codomain)then
          native_error "native record fields cannot depend on previous values";
        let rec monomorphic env term =
          (match EConstr.kind sigma term with
           |Prod(_,domain,_)when is_sort env sigma domain->
             native_error "polymorphic native record fields are not supported"
           |_->());
          EConstr.iter_with_full_binders env sigma EConstr.push_rel monomorphic env term in
        monomorphic env domain;
        let field_type=try ocaml_type env sigma vars domain with Not_ocaml why->
          CErrors.user_err(str "OCaml Native record field: "++why)in
        let env=EConstr.push_rel(Context.Rel.Declaration.LocalAssum(na,domain))env in
        ({SomaForeign.field_name=name;field_type;field_mutable=false},projection)::
          fields env(None::vars)codomain rest
      |_->native_error "unsupported checked record field shape"in
  let checked=fields parameter_env vars typ structure.projections in
  if checked=[]then native_error "a native record alias needs at least one field";
  let logical_type=KerName.to_string(MutInd.canonical(fst ind))in
  if List.exists(fun info->info.SomaForeign.enum_logical_type=logical_type)!native_enums then
    native_error "one logical type cannot mix native record and variant aliases";
  if List.exists(fun info->info.SomaForeign.record_alias_logical_type=logical_type &&
       info.record_alias_target<>target)!native_record_aliases then
    native_error "one logical record cannot use conflicting native types";
  let c=native_declare name(CAst.make(Constrexpr.CRef(source,None)))None in
  native_register name c(if params=[]then SomaForeign.OCamlNativeType target else
    SomaForeign.OCamlNativeExternalFamily(params,target));
  let source=match !SomaImport.source_file with Some f->SomaImport.project_file f|None->assert false in
  Lib.add_leaf(in_native_record_alias SomaForeign.{record_alias_constant=c;
    record_alias_logical_type=logical_type;record_alias_target=target;
    record_alias_parameters=params;record_alias_fields=List.map fst checked;
    record_alias_projections=List.map snd checked;record_alias_source=source})

(* The opaque handle has no pure mutable fields. Anonymous type-valued lets
   retain checked schema dependencies in the kernel term for module discovery
   and hashing, without exposing a projection or evaluating any native value. *)
let native_record ?(logical=false) name fields =
  ignore(native_context());
  if not(Rocqlib.has_ref "soma.native.handle")then native_error "import Soma.Native first";
  if fields=[]then native_error "an owned record must have fields";
  let names=List.map(fun(id,_,_)->Id.to_string id)fields in
  List.iter(fun field->ignore(native_path field))names;
  if List.length(List.sort_uniq String.compare names)<>List.length names then
    native_error "owned record fields must be distinct";
  let env=Global.env()in
  let checked=List.map(fun(id,mutable_,syntax)->
    let sigma,typ=Constrintern.interp_type_evars env(Evd.from_env env)syntax in
    let rec monomorphic t =
      (match EConstr.kind sigma t with
       | Prod(_,domain,_) when EConstr.isSort sigma domain -> native_error "polymorphic owned fields are not supported"
       | _->());EConstr.iter sigma monomorphic t in
    monomorphic typ;
    let field_type=try ocaml_type env sigma [] typ with Not_ocaml why->
      CErrors.user_err(str "OCaml Native owned field: "++why)in
    syntax,{SomaForeign.field_name=Id.to_string id;field_type;field_mutable=mutable_})fields in
  if logical && List.exists(fun(_,f)->f.SomaForeign.field_mutable)checked then
    native_error "immutable record fields cannot be mutable";
  let namespace=native_namespace()in
  let logical_info=if not logical then None else begin
    let hidden=Id.of_string("SomaNativeRecord_"^Id.to_string name)in
    let builder=Id.of_string("Build_"^Id.to_string name)in
    let projection_flags=Record.Data.{pf_coercion=None;pf_instance=None;pf_canonical=false}in
    let record=Record.Ast.{name=CAst.make hidden;is_coercion=Vernacexpr.NoCoercion;
      binders=[];cfs=List.map2(fun(id,_,syntax)_ ->
       Vernacexpr.AssumExpr(CAst.make(Name id),[],syntax),projection_flags,[])fields checked;
      idbuild=CAst.make builder;sort=None;default_inhabitant_id=None}in
    let flags=ComInductive.{poly=PolyFlags.default;template=None;finite=Declarations.BiFinite;
      mode=None;schemes=DeclareInd.Default}in
    let before=Environ.fold_constants(fun c _ set->Cset_env.add c set)(Global.env())Cset_env.empty in
    ignore(Record.definition_structure ~flags None Vernacexpr.Record ~primitive_proj:false [record]);
    let definitions=Environ.fold_constants(fun c _ all->if Cset_env.mem c before then all else
      KerName.to_string(Constant.canonical c)::all)(Global.env())[]in
    Some SomaForeign.{logical_type=namespace^"."^Id.to_string hidden;
      logical_constructor=namespace^"."^Id.to_string builder;
      logical_projections=List.map(fun(id,_,_)->namespace^"."^Id.to_string id)fields;
      logical_definitions=List.sort String.compare definitions}
  end in
  let symbol=namespace^"."^Id.to_string name in
  let handle=native_app(native_global "soma.native.handle")[native_string symbol]in
  let body=List.fold_right(fun(syntax,_)rest->
    CAst.make(Constrexpr.CLetIn(CAst.make Anonymous,syntax,None,rest)))checked handle in
  let body=match logical_info with None->body|Some info->
    CAst.make(Constrexpr.CRef(Libnames.qualid_of_string info.logical_type,None))in
  let c=native_declare name body None in
  let source=match !SomaImport.source_file with Some f->SomaImport.project_file f|None->assert false in
  let record=SomaForeign.{record_namespace=namespace;record_name=Id.to_string name;
    record_source=source;record_fields=List.map snd checked}in
  native_register name c (match logical_info with None->SomaForeign.OCamlNativeOwnedRecord record
   |Some info->SomaForeign.OCamlNativeImmutableRecord(record,info))

(* Closed native tag schemas are checked types, not handwritten conversion
   callbacks. Type-valued lets retain every payload's logical dependencies. *)
let native_variant_tag tag =
  let letter=function 'a'..'z'|'A'..'Z'->true|_->false in
  if tag="" || not(letter tag.[0]) || List.mem tag keywords ||
     not(String.for_all(function 'a'..'z'|'A'..'Z'|'0'..'9'|'_'|'\''->true|_->false)tag)
  then native_error "a polymorphic variant tag must be an OCaml identifier";
  tag
let native_variant_tag_hash tag =
  let h=String.fold_left(fun h c->Int64.logand 0x7fffffffL
    (Int64.add(Int64.mul 223L h)(Int64.of_int(Char.code c))))0L tag in
  Int64.to_int h
let native_variant ?(parameters=[]) ?(open_row=false) name cases =
  ignore(native_context());
  if not(Rocqlib.has_ref "soma.native.handle")then native_error "import Soma.Native first";
  if cases=[]then native_error "a polymorphic variant needs at least one tag";
  if open_row && List.length parameters<>1 then native_error "an open variant needs exactly one row type parameter";
  let tags=List.map(fun(tag,_)->native_variant_tag tag)cases in
  if List.length(List.sort_uniq String.compare tags)<>List.length tags then
    native_error "polymorphic variant tags must be distinct";
  let hashes=List.map native_variant_tag_hash tags in
  if List.length(List.sort_uniq Int.compare hashes)<>List.length hashes then
    native_error "polymorphic variant tag hash collision";
  let env=Global.env()in
  let ids=List.map fst parameters in
  if List.length(List.sort_uniq Id.compare ids)<>List.length ids then native_error "native type parameters must be distinct";
  let binders=List.map(fun(id,typ)->
    let sigma,checked=Constrintern.interp_type_evars env(Evd.from_env env)typ in
    (match EConstr.kind sigma checked with
     |Sort sort when not(EConstr.ESorts.is_prop sigma sort || EConstr.ESorts.is_sprop sigma sort)->()
     |_->native_error "native type parameters must have sort Type or Set");
    Constrexpr.CLocalAssum([CAst.make(Name id)],None,Constrexpr.Default Glob_term.Explicit,typ))parameters in
  let wrap_type typ=if binders=[]then typ else CAst.make(Constrexpr.CProdN(binders,typ))in
  let rec enter env sigma vars =function
    |0,t->env,vars,t
    |n,t->match EConstr.kind sigma t with
      |Prod(binder,domain,codomain)->
        let variable=type_variable(List.filter_map Fun.id vars)binder.Context.binder_name in
        enter(EConstr.push_rel(Context.Rel.Declaration.LocalAssum(binder,domain))env)sigma(Some variable::vars)(n-1,codomain)
      |_->assert false in
  let checked=List.map(fun(tag,syntax)->
    let payload=Option.map(fun syntax->
      let sigma,typ=Constrintern.interp_type_evars env(Evd.from_env env)(wrap_type syntax)in
      let env,vars,typ=enter env sigma [] (List.length parameters,typ)in
      let rec monomorphic t =
        (match EConstr.kind sigma t with
         | Prod(_,domain,_) when EConstr.isSort sigma domain -> native_error "polymorphic variant payloads must be monomorphic"
         | _->());EConstr.iter sigma monomorphic t in
      monomorphic typ;
      if open_row && not(EConstr.Vars.noccurn sigma 1 typ)then
        native_error "an open variant row parameter cannot occur in a payload";
      try ocaml_type env sigma vars typ,EConstr.isProd sigma(Reductionops.whd_all env sigma typ) with Not_ocaml why->
        CErrors.user_err(str "OCaml Native variant payload: "++why))syntax in
    syntax,{SomaForeign.case_tag=tag;case_payload=Option.map fst payload;
      case_is_function=(match payload with None->false|Some(_,fn)->fn)})cases in
  let namespace=native_namespace()in
  let type_args=List.map(fun id->CAst.make(Constrexpr.CRef(Libnames.qualid_of_ident id,None)))ids in
  let rec pack=function []->native_global "core.unit.type"|[arg]->arg|arg::rest->native_app(native_global "core.prod.type")[arg;pack rest]in
  let handle=if binders=[]then native_app(native_global "soma.native.handle")[native_string(namespace^"."^Id.to_string name)]else
    native_app(native_global "soma.native.family")[native_string(namespace^"."^Id.to_string name);pack type_args]in
  let body=List.fold_right(fun(syntax,_)rest->match syntax with None->rest|Some typ->
    CAst.make(Constrexpr.CLetIn(CAst.make Anonymous,typ,None,rest)))checked handle in
  let body=if binders=[]then body else CAst.make(Constrexpr.CLambdaN(binders,body))in
  let c=native_declare name body None in
  let source=match !SomaImport.source_file with Some f->SomaImport.project_file f|None->assert false in
  let variant={SomaForeign.variant_namespace=namespace;variant_name=Id.to_string name;variant_source=source;variant_cases=List.map snd checked}in
  let params=List.rev(fst(List.fold_left(fun(names,used)(id,_)->let name=type_variable used(Name id)in name::names,name::used)([],[])parameters))in
  native_register name c (if open_row then SomaForeign.OCamlNativeOpenVariant(List.hd params,variant)
   else if params=[]then SomaForeign.OCamlNativeOwnedVariant variant else SomaForeign.OCamlNativeParametricVariant(params,variant))

(* Leading type parameters form an opaque native family. Keep the checked
   signature in a type-valued let so Apply instantiates logical types rather
   than replacing generated OCaml strings. Existing monomorphic metadata stays
   byte-for-byte unchanged. *)
let native_callable ?(optional=[]) name syntax =
  ignore(native_context());
  if not(Rocqlib.has_ref "soma.native.handle")then native_error "import Soma.Native first";
  let env=Global.env()in
  let sigma,typ=Constrintern.interp_type_evars env(Evd.from_env env)syntax in
  let rec enter env vars parameters ids typ=match EConstr.kind sigma typ with
    |Prod(binder,domain,codomain)when is_sort env sigma domain->
      (match EConstr.kind sigma domain,binder.Context.binder_name with
       |Sort sort,Name _ when not(EConstr.ESorts.is_prop sigma sort || EConstr.ESorts.is_sprop sigma sort)->()
       |_->native_error "native callable type parameters must be named Type or Set");
      let id=match binder.Context.binder_name with Name id->id|_->assert false in
      if List.mem id ids then native_error "native callable type parameters must be distinct";
      let variable=type_variable(List.filter_map Fun.id vars)binder.Context.binder_name in
      let ast=Constrextern.extern_constr ~flags:(PrintingFlags.current())env sigma domain in
      let parameter=Constrexpr.CLocalAssum([CAst.make binder.Context.binder_name],None,Constrexpr.Default Glob_term.Explicit,ast)in
      enter(EConstr.push_rel(Context.Rel.Declaration.LocalAssum(binder,domain))env)(Some variable::vars)
        (parameters@[parameter])(ids@[id])codomain
    |_->env,vars,parameters,ids,typ in
  let env,vars,parameters,ids,typ=enter env [] [] [] typ in
  let rec monomorphic t=
    (match EConstr.kind sigma t with
     |Prod(_,domain,_)when is_sort env sigma domain->native_error "native callable arguments must be monomorphic"
     |_->());EConstr.iter sigma monomorphic t in
  let rec signature args labels t =
    match EConstr.kind sigma(Reductionops.whd_all env sigma t)with
    | Prod(binder,domain,codomain)->
      if is_sort env sigma domain then native_error "native callable type parameters must precede values";
      if not(EConstr.Vars.noccurn sigma 1 codomain)then native_error "native callable result depends on a value";
      monomorphic domain;
      let label=match binder.Context.binder_name with
        | Anonymous->None
        | Name id->
          let label=ocaml_name ~definition:"native callable"(Id.to_string id)in
          if List.mem id optional then begin
            let head,payload=EConstr.decompose_app sigma(Reductionops.whd_all env sigma domain)in
            if Array.length payload<>1 || not(EConstr.isRefX env sigma(Rocqlib.lib_ref "core.option.type")head)then
              native_error "an optional callable argument must have type option";
            Some("?"^label)
          end else Some label in
      let arg=try ocaml_type env sigma vars domain with Not_ocaml why->CErrors.user_err(str "OCaml Native callable: "++why)in
      (match label with
       | Some label when String.starts_with ~prefix:"?" label &&
           not(String.ends_with ~suffix:" option" arg)->
         native_error "an optional callable argument must use the native option representation"
       | _->());
      signature(arg::args)(label::labels)(EConstr.Vars.subst1(EConstr.mkProp)codomain)
    | _->
      monomorphic t;
      let result=try ocaml_type env sigma vars t with Not_ocaml why->CErrors.user_err(str "OCaml Native callable: "++why)in
      List.rev args,List.rev labels,result in
  let args,labels,result=signature[][]typ in
  let optional_labels=List.map(fun id->Some("?"^Id.to_string id))optional in
  let observed_optional=List.filter(function
    | Some label->String.starts_with ~prefix:"?" label
    | None->false)labels in
  if List.sort compare optional_labels<>List.sort compare observed_optional then
    native_error "Optional must list each optional callable value argument exactly once";
  if args=[]then native_error "a native callable needs at least one argument";
  let namespace=native_namespace()in
  let type_args=List.map(fun id->CAst.make(Constrexpr.CRef(Libnames.qualid_of_ident id,None)))ids in
  let rec pack=function []->native_global "core.unit.type"|[arg]->arg|arg::rest->native_app(native_global "core.prod.type")[arg;pack rest]in
  let handle=if parameters=[]then native_app(native_global "soma.native.handle")[native_string(namespace^"."^Id.to_string name)]
    else native_app(native_global "soma.native.family")[native_string(namespace^"."^Id.to_string name);pack type_args]in
  let checked=if parameters=[]then syntax else Constrextern.extern_constr ~flags:(PrintingFlags.current())env sigma typ in
  let body=CAst.make(Constrexpr.CLetIn(CAst.make Anonymous,checked,None,handle))in
  let body=if parameters=[]then body else CAst.make(Constrexpr.CLambdaN(parameters,body))in
  let c=native_declare name body None in
  let source=match !SomaImport.source_file with Some f->SomaImport.project_file f|None->assert false in
  let info={SomaForeign.callable_namespace=namespace;callable_name=Id.to_string name;callable_source=source;
    callable_arguments=args;callable_labels=labels;callable_result=result}in
  let params=List.rev(List.filter_map Fun.id vars)in
  native_register name c(if params=[]then SomaForeign.OCamlNativeCallableType info
    else SomaForeign.OCamlNativeParametricCallable(params,info))
let native_callable_type ?(required="Apply needs a declared native callable as its first argument") env sigma type_vars typ =
  let head,args=EConstr.decompose_app sigma typ in
  match EConstr.kind sigma head with
  | Const(c,_)->(match Cmap_env.find_opt c !bindings with
    | Some{item=SomaForeign.OCamlNativeCallableType info;_}when Array.length args=0->info
    | Some{item=SomaForeign.OCamlNativeParametricCallable(params,info);_}when List.length params=Array.length args->
      let body=match(Environ.lookup_constant c env).Declarations.const_body with
        |Declarations.Def body->EConstr.of_constr body
        |_->native_error "a native callable must retain its checked signature"in
      let body=Array.fold_left(fun body argument->match EConstr.kind sigma body with
        |Lambda(_,_,rest)->EConstr.Vars.subst1 argument rest
        |_->native_error "native callable parameter count differs from its definition")body args in
      let signature=match EConstr.kind sigma body with
        |LetIn(_,signature,_,_)->signature
        |_->native_error "native callable differs from its checked signature"in
      (* Only the schema's original value binders are callable inputs.
         Instantiation may expose an arrow in its result parameter; preserve
         that entire returned function and its partial-application boundary. *)
      let rec instantiate remaining previous typ=
        if remaining=0 then List.rev previous,ocaml_type env sigma type_vars typ else
        match EConstr.kind sigma(Reductionops.whd_all env sigma typ)with
        |Prod(_,domain,codomain)->
          instantiate(remaining-1)(ocaml_type env sigma type_vars domain::previous)
            (EConstr.Vars.subst1(EConstr.mkProp)codomain)
        |_->native_error "native callable has fewer value binders than its checked signature" in
      let arguments,result=instantiate(List.length info.SomaForeign.callable_arguments)[] signature in
      {info with SomaForeign.callable_arguments=arguments;callable_result=result}
    | _->native_error required)
  | _->native_error required

let native_constructor_path path =
 let parts=String.split_on_char '.' path in
 if parts=[] || List.exists(fun part->not(is_module_name part) || part.[0]<>Char.uppercase_ascii part.[0])parts then
  native_error "a constructor path needs uppercase OCaml module/constructor names";
 path

type algebraic_fields = (Id.t * bool * Constrexpr.constr_expr) list

type algebraic_case =
  | Arguments of Constrexpr.constr_expr list
  | Inline_record of algebraic_fields

type algebraic_member =
  | Record_fields of algebraic_fields
  | Variant_cases of (string * algebraic_case) list

let native_algebraic ?(exceptions=[]) name members =
  ignore (native_context ());
  if not (Rocqlib.has_ref "soma.native.handle") then native_error "import Soma.Native first";
  let namespace = native_namespace () in
  let checked_name id = native_path (Id.to_string id) in
  let ids = List.map fst members in
  let names = List.map checked_name ids in
  let distinct category names =
    if List.length (List.sort_uniq String.compare names) <> List.length names then
      native_error (category ^ " must be distinct") in
  distinct "algebraic type names" names;
  let formals = List.map (fun name -> CAst.make (Name name)) ids in
  let sort = CAst.make (Constrexpr.CSort Constrexpr_ops.expr_Type_sort) in
  let binders = [Constrexpr.CLocalAssum (formals, None, Constrexpr.Default Glob_term.Explicit, sort)] in
  let scope syntax = CAst.make (Constrexpr.CProdN (binders, syntax)) in
  let logical_dependencies = ref [] in
  let checked_type syntax =
    let scoped = scope syntax in
    logical_dependencies := scoped :: !logical_dependencies;
    let env = Global.env () in
    let sigma, typ = Constrintern.interp_type_evars env (Evd.from_env env) scoped in
    let rec enter env vars typ = function
      | [] -> env, vars, typ
      | name :: rest ->
        match EConstr.kind sigma typ with
        | Prod (binder, dom, cod) ->
          let env = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (binder, dom)) env in
          enter env (Some name :: vars) cod rest
        | _ -> assert false in
    let env, vars, typ = enter env [] typ names in
    let rec monomorphic typ =
      (match EConstr.kind sigma typ with
       | Prod (_, domain, _) when is_sort env sigma domain ->
         native_error "algebraic fields and constructor arguments must be monomorphic"
       | _ -> ());
      EConstr.iter sigma monomorphic typ in
    monomorphic typ;
    try ocaml_type env sigma vars typ with Not_ocaml why ->
      CErrors.user_err (str "OCaml Native algebraic member: " ++ why) in
  let fields declarations =
    let result = List.map (fun (id, mutable_, syntax) ->
      { SomaForeign.field_name = checked_name id;
        field_type = checked_type syntax; field_mutable = mutable_ }) declarations in
    distinct "algebraic record field names" (List.map (fun f -> f.SomaForeign.field_name) result);
    result in
  let case (name, body) =
    if String.contains name '.' then native_error "an algebraic constructor is a single name";
    let name = native_constructor_path name in
    let body = match body with
      | Arguments args -> SomaForeign.Constructor_arguments (List.map checked_type args)
      | Inline_record form -> SomaForeign.Constructor_record (fields form) in
    name, body in
  let body = function
    | Record_fields declarations -> SomaForeign.Algebraic_record (fields declarations)
    | Variant_cases declarations ->
      let cases = List.map case declarations in
      distinct "algebraic constructor names" (List.map fst cases);
      SomaForeign.Algebraic_variant cases in
  let source = match !SomaImport.source_file with
    | Some file -> SomaImport.project_file file
    | None -> assert false in
  let exceptions = List.map case exceptions in
  distinct "algebraic exception names" (List.map fst exceptions);
  let group = {
    SomaForeign.algebraic_namespace = namespace;
    algebraic_name = Id.to_string name;
    algebraic_source = source;
    algebraic_members = List.map2 (fun name (_, form) -> name, body form) names members;
    algebraic_exceptions = exceptions;
  } in
  List.iter2 (fun id member ->
    let handle = native_app (native_global "soma.native.handle") [native_string (namespace ^ "." ^ member)] in
    (* Every member carries the group's actual field-type dependencies. The
       bound type names stand for local members only while checking schemas. *)
    let body = List.fold_left (fun rest dependency ->
      CAst.make (Constrexpr.CLetIn (CAst.make Anonymous, dependency, None, rest))) handle !logical_dependencies in
    let constant = native_declare id body None in
    native_register id constant (SomaForeign.OCamlNativeAlgebraic (group, member))) ids names
let native_owned_exception owner constructor =
  let key, _, _ = native_context () in
  match Nametab.locate (Libnames.qualid_of_ident owner) with
  | GlobRef.ConstRef c ->
    (match Cmap_env.find_opt c !bindings with
     | Some { item = SomaForeign.OCamlNativeAlgebraic (group, _); key = binding_key; _ }
       when key = binding_key ->
       if not (List.mem_assoc constructor group.SomaForeign.algebraic_exceptions) then
         native_error "the algebraic group does not declare this exception";
       SomaForeign.native_algebraic_module group ^ "." ^ constructor
     | _ -> native_error "an owned exception needs an algebraic member declared in this definition")
  | _ -> native_error "an owned exception needs an algebraic member"

let primitive_symbol symbol =
  let first = function 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false in
  let rest = function '0'..'9' -> true | c -> first c in
  if symbol = "" || not (first symbol.[0]) || not (String.for_all rest symbol) then
    native_error "a primitive symbol must be a C identifier";
  symbol

let native_callback name typ operation =
  ignore (native_context ());
  if not (Rocqlib.has_ref "soma.native.callback") then native_error "import Soma.Native first";
  let env = Global.env () in
  let sigma, typ = Constrintern.interp_type_evars env (Evd.from_env env) typ in
  let rec enter env vars parameters typ=match EConstr.kind sigma typ with
    |Prod(binder,domain,codomain)when is_sort env sigma domain->
      (match EConstr.kind sigma domain,binder.Context.binder_name with
       |Sort sort,Name _ when not(EConstr.ESorts.is_prop sigma sort || EConstr.ESorts.is_sprop sigma sort)->()
       |_->native_error "native descriptor type parameters must be named Type or Set");
      let variable=type_variable(List.filter_map Fun.id vars)binder.Context.binder_name in
      let ast=Constrextern.extern_constr ~flags:(PrintingFlags.current())env sigma domain in
      let parameter=Constrexpr.CLocalAssum([CAst.make binder.Context.binder_name],None,Constrexpr.Default Glob_term.Explicit,ast)in
      enter(EConstr.push_rel(Context.Rel.Declaration.LocalAssum(binder,domain))env)(Some variable::vars)(parameters@[parameter])codomain
    |_->env,vars,parameters,typ in
  let env,type_vars,type_parameters,typ=enter env [] [] typ in
  let fixed_arity = match operation with
    | SomaForeign.NativeGet _ | SomaForeign.NativeInlineGet _ | SomaForeign.NativeCallableWrap _ | SomaForeign.NativeCallableWrapFull _ -> Some 1
    | SomaForeign.NativeSet _ | SomaForeign.NativeInlineSet _ -> Some 2
    | SomaForeign.NativeBuild fields | SomaForeign.NativeInlineBuild (_, fields)
    | SomaForeign.NativeBuildEvaluating (fields, _) -> Some (List.length fields)
    | SomaForeign.NativeConstructorBuild(_,arity) -> Some (max 1 arity)
    | SomaForeign.NativeCopy fields -> Some(1+List.length fields)
    | SomaForeign.NativeCallableApply _ ->
      (match EConstr.kind sigma(Reductionops.whd_all env sigma typ)with
       | Prod(_,domain,_)->Some(1+List.length(native_callable_type env sigma type_vars domain).SomaForeign.callable_arguments)
       | _->native_error "Apply needs a native callable argument")
    | SomaForeign.NativeValue _ | SomaForeign.NativeExternalValue _ | SomaForeign.NativeExternalLiteralCallback _
    | SomaForeign.NativePrimitive _ -> None
    | SomaForeign.NativeVariantView _ | SomaForeign.NativeVariantBuild _
    | SomaForeign.NativeConstructorTag _ | SomaForeign.NativeConstructorCase _
    | SomaForeign.NativeRecordFactory _ | SomaForeign.NativeVariantDispatch _ | SomaForeign.NativeGetFunction _ | SomaForeign.NativeSetFunction _
    | SomaForeign.NativeExternalConstant _ | SomaForeign.NativeExternalLiteralConstant _ | SomaForeign.NativeExternalComposedValue _
    | SomaForeign.NativeExternalTransformedComposition _
    | SomaForeign.NativeExternalException _ | SomaForeign.NativeCallableApplyFunction _
    | SomaForeign.NativeStaticInvocation _ | SomaForeign.NativeStaticApplication _ | SomaForeign.NativeVariantFunction _
    | SomaForeign.NativeStaticCompositionScope _ | SomaForeign.NativeStaticFunction _
    | SomaForeign.NativeExternalInsertedLiteralFunction _ | SomaForeign.NativeExternalFieldsFunction _
    | SomaForeign.NativeFloatConstant _ | SomaForeign.NativeExternalLiteralFunction _
    | SomaForeign.NativeAssertionFunction _ | SomaForeign.NativeAssertionFactory _ | SomaForeign.NativeAssertionFunctionFactory _ | SomaForeign.NativeExternalThunkFactory _
    | SomaForeign.NativeVariantFactory _ | SomaForeign.NativeDeferredFields _ | SomaForeign.NativeDefaultedFunction _ | SomaForeign.NativeBoundBooleanFunction _ -> Some 1 in
  let rec arguments previous remaining t =
    if remaining=Some 0 then List.rev previous,t else
    (* Leave native aliases intact: they denote opaque external types. *)
    let head,_=EConstr.decompose_app sigma t in
    let known = match EConstr.kind sigma head with Const(c,_) -> Cmap_env.mem c !bindings | _ -> false in
    let t = if known then t else Reductionops.whd_all env sigma t in
    match EConstr.kind sigma t with
    | Prod (binder, domain, codomain) ->
      if is_sort env sigma domain then native_error "polymorphic native descriptors are not supported yet";
      if not (EConstr.Vars.noccurn sigma 1 codomain) then native_error "a native result cannot depend on a value";
      let label = match binder.Context.binder_name with
        | Name id -> Some (ocaml_name ~definition:"native callback" (Id.to_string id))
        | Anonymous -> None in
      arguments ((domain,label)::previous) (Option.map pred remaining) (EConstr.Vars.subst1 (EConstr.mkProp) codomain)
    | _ -> List.rev previous,t in
  let args, result = arguments [] fixed_arity typ in
  if args=[] then native_error "a callback declaration needs at least one argument";
  let args_types, labels = List.split args in
  let types = try List.map (ocaml_type env sigma type_vars) args_types,ocaml_type env sigma type_vars result
    with Not_ocaml why -> CErrors.user_err (str "OCaml Native: " ++ why) in
  let argument_names,result_name = types in
  let field name =
    if String.contains name '.' then native_error "a field is a single name";
    native_path name in
  let external_shape t =
    let head, args = EConstr.decompose_app sigma t in
    match EConstr.kind sigma head with
    | Const (c, _) -> (match Cmap_env.find_opt c !bindings with
      | Some {item=SomaForeign.OCamlNativeExternalFamily (params, _); _}
        when Array.length args = List.length params -> Some `External
      | Some {item=(SomaForeign.OCamlNativeType _ | SomaForeign.OCamlNativeAlgebraic _); _}
        when Array.length args = 0 -> Some `External
      | Some {item=(SomaForeign.OCamlNativeOwnedRecord _|SomaForeign.OCamlNativeImmutableRecord _); _}
        when Array.length args = 0 -> Some `Record
      | _ -> None)
    | _ -> None in
  let record_type t =
    match external_shape t with
    | Some _ -> ()
    | None -> native_error "a record operation needs a declared native type" in
  let variant_type ?(allow_open=false) t =
    let head,args=EConstr.decompose_app sigma t in
    match EConstr.kind sigma head with
    | Const(c,_) -> (match Cmap_env.find_opt c !bindings with
      | Some {item=SomaForeign.OCamlNativeOpenVariant(_,v);_} when Array.length args=1->
        if not allow_open then native_error "an open variant cannot be viewed exhaustively";
        v
      | Some {item=SomaForeign.OCamlNativeOwnedVariant v;_} when Array.length args=0->v
      | Some {item=SomaForeign.OCamlNativeParametricVariant(params,v);_} when Array.length args=List.length params->
        (* Instantiate checked logical payload types, rather than substituting
           OCaml strings: an argument may itself be an arrow/product/schema. *)
        let body=match(Environ.lookup_constant c env).Declarations.const_body with
          |Declarations.Def body->EConstr.of_constr body
          |_->native_error "a native schema must retain its checked definition"in
        let body=Array.fold_left(fun body argument->match EConstr.kind sigma body with
          |Lambda(_,_,rest)->EConstr.Vars.subst1 argument rest
          |_->native_error "native schema parameter count differs from its definition")body args in
        let rec instantiate body=function
          |[]->[]
          |case::rest->match case.SomaForeign.case_payload with
            |None->case::instantiate body rest
            |Some _->match EConstr.kind sigma body with
              |LetIn(_,payload,_,following)->
                let spelling=ocaml_type env sigma type_vars payload in
                let fn=EConstr.isProd sigma(Reductionops.whd_all env sigma payload)in
                {case with SomaForeign.case_payload=Some spelling;case_is_function=fn}::
                 instantiate(EConstr.Vars.subst1 payload following)rest
              |_->native_error "native schema payload differs from its checked definition"in
        {v with SomaForeign.variant_cases=instantiate body v.SomaForeign.variant_cases}
      | _->native_error "a variant operation needs a declared native polymorphic variant")
    | _->native_error "a variant operation needs a declared native polymorphic variant" in
  let constructor_type t =
    if not (EConstr.isRefX env sigma (Rocqlib.lib_ref "soma.exception_value.type") t ||
            external_shape t = Some `External)
    then native_error "constructor operations need a declared native type" in
  (match operation with
   | SomaForeign.NativeDeferredFields _ | SomaForeign.NativeDefaultedFunction _ | SomaForeign.NativeBoundBooleanFunction _
   | SomaForeign.NativeRecordFactory _ | SomaForeign.NativeVariantDispatch _ | SomaForeign.NativeGetFunction _ | SomaForeign.NativeSetFunction _
   | SomaForeign.NativeExternalConstant _ | SomaForeign.NativeExternalLiteralConstant _ | SomaForeign.NativeExternalComposedValue _
   | SomaForeign.NativeExternalTransformedComposition _
   | SomaForeign.NativeExternalException _
   | SomaForeign.NativeAssertionFunction _ | SomaForeign.NativeAssertionFactory _ | SomaForeign.NativeAssertionFunctionFactory _ | SomaForeign.NativeExternalThunkFactory _
   | SomaForeign.NativeVariantFactory _
   | SomaForeign.NativeStaticInvocation _ | SomaForeign.NativeStaticApplication _ | SomaForeign.NativeVariantFunction _
    | SomaForeign.NativeStaticCompositionScope _ | SomaForeign.NativeStaticFunction _
   | SomaForeign.NativeExternalInsertedLiteralFunction _ | SomaForeign.NativeExternalFieldsFunction _
   | SomaForeign.NativeExternalLiteralFunction _ | SomaForeign.NativeFloatConstant _ | SomaForeign.NativeValue _ | SomaForeign.NativeExternalValue _ | SomaForeign.NativeExternalLiteralCallback _ | SomaForeign.NativePrimitive _ | SomaForeign.NativeCallableApply _ | SomaForeign.NativeCallableApplyFunction _ | SomaForeign.NativeCallableWrap _ | SomaForeign.NativeCallableWrapFull _ | SomaForeign.NativeVariantView _ | SomaForeign.NativeVariantBuild _ -> ()
   | SomaForeign.NativeConstructorTag _ | SomaForeign.NativeConstructorCase _
   | SomaForeign.NativeInlineGet _ | SomaForeign.NativeInlineSet _ ->
     constructor_type (List.hd args_types)
   | SomaForeign.NativeConstructorBuild _ | SomaForeign.NativeInlineBuild _ -> constructor_type result
   | SomaForeign.NativeBuild _ | SomaForeign.NativeBuildEvaluating _ -> record_type result
   | SomaForeign.NativeCopy _ -> record_type(List.hd args_types);record_type result
   | SomaForeign.NativeGet _ | SomaForeign.NativeSet _ -> record_type(List.hd args_types));
  (* References within the owned schema use local type names; checked
     handler types name the same members through their generated module. *)
  let local_record_type prefix annotation =
    let buffer = Buffer.create (String.length annotation) in
    let rec copy start =
      match CString.string_index_from annotation start prefix with
      | stop ->
        Buffer.add_substring buffer annotation start (stop - start);
        copy (stop + String.length prefix)
      | exception Not_found ->
        Buffer.add_substring buffer annotation start (String.length annotation - start) in
    copy 0;
    Buffer.contents buffer in
  let owned_record_field operation receiver name =
    let head, type_args = EConstr.decompose_app sigma receiver in
    let fields, local = match EConstr.kind sigma head with
        | Const (c, _) when Array.length type_args = 0 ->
          (match Cmap_env.find_opt c !bindings with
          | Some { item = SomaForeign.OCamlNativeAlgebraic (group, member); _ } ->
            (match List.assoc member group.SomaForeign.algebraic_members with
            | SomaForeign.Algebraic_record fields ->
              fields, local_record_type (SomaForeign.native_algebraic_module group ^ ".")
            | _ -> native_error (operation ^ " needs a native record"))
          | Some { item = (SomaForeign.OCamlNativeOwnedRecord record
                        | SomaForeign.OCamlNativeImmutableRecord (record, _)); _ } ->
            record.SomaForeign.record_fields, Fun.id
          | _ -> native_error (operation ^ " needs an owned native record"))
        | _ -> native_error (operation ^ " needs an owned native record") in
    let name = field name in
    let declaration = match List.find_opt (fun f -> f.SomaForeign.field_name = name) fields with
        | Some declaration -> declaration
        | None -> native_error (operation ^ " field is absent from its schema") in
    name, declaration, local in
  let static_shape typ =
        let head,_=EConstr.decompose_app sigma typ in
        let callable=match EConstr.kind sigma head with
          |Const(c,_)->(match Cmap_env.find_opt c !bindings with
            |Some {item=(SomaForeign.OCamlNativeCallableType _|SomaForeign.OCamlNativeParametricCallable _);_}->true
            |_->false)|_->false in
        if callable then let c=native_callable_type env sigma type_vars typ in
          c.SomaForeign.callable_arguments,c.callable_labels,c.callable_result
        else let params,answer=arguments [] None typ in
          List.map(fun(t,_)->ocaml_type env sigma type_vars t)params,
          List.map snd params,ocaml_type env sigma type_vars answer in
  let static_descriptor name =
        let c=match Nametab.locate(Libnames.qualid_of_string name)with
          |GlobRef.ConstRef c->c|_->native_error "a static input needs a declared native getter" in
        let n=match Cmap_env.find_opt c !bindings with
          |Some {item=SomaForeign.OCamlNativeCallback n;_}->n
          |_->native_error "a static input needs a declared native getter" in
        if n.SomaForeign.arguments<>["unit"] || n.labels<>[None] then
          native_error "a static input needs a unit native getter";
        let typ=EConstr.of_constr(Environ.lookup_constant c env).Declarations.const_type in
        let rec instantiate index typ =match EConstr.kind sigma(Reductionops.whd_all env sigma typ)with
          |Prod(_,domain,rest)when is_sort env sigma domain ->
            if index>=List.length type_vars then native_error "static input type parameters exceed the result's parameters";
            instantiate(index+1)(EConstr.Vars.subst1(EConstr.mkRel(List.length type_vars-index))rest)
          |_->typ in
        let typ=instantiate 0 typ in
        let head,args=EConstr.decompose_app sigma(Reductionops.whd_betaiotazeta env sigma typ)in
        if Array.length args<>2 || not(EConstr.isRefX env sigma(Rocqlib.lib_ref "soma.native.callback")head)then
          native_error "a static input needs a native callback type";
        n.operation,args.(1) in
  let operation = match operation with
    | SomaForeign.NativeExternalThunkFactory(path,literal) ->
      if argument_names<>["unit"] then native_error "a closed thunk factory needs a unit getter";
      let parameters,_=arguments [] (Some 2) result in
      (match parameters with
       | [(first,None);(second,None)]
         when EConstr.isRefX env sigma (Rocqlib.lib_ref "core.unit.type") first &&
              EConstr.isRefX env sigma (Rocqlib.lib_ref "core.unit.type") second -> ()
       | _ -> native_error "a closed thunk factory has type unit -> unit -> answer");
      SomaForeign.NativeExternalThunkFactory(native_external_path path,literal)
    | SomaForeign.NativeVariantFactory(tag,_) ->
      if argument_names<>["unit"] then native_error "a variant factory needs a unit getter";
      let parameters,answer=arguments [] (Some 2) result in
      let payload=match parameters with
       | [(first,None);(payload,None)]
         when EConstr.isRefX env sigma (Rocqlib.lib_ref "core.unit.type") first -> payload
       | _ -> native_error "a variant factory has type unit -> payload -> variant" in
      let v=variant_type ~allow_open:true answer in
      let tag=native_variant_tag tag in
      let case=match List.find_opt(fun c->c.SomaForeign.case_tag=tag)v.variant_cases with
       |Some case->case|None->native_error "factory tag is absent from the native variant" in
      if ocaml_type env sigma type_vars payload<>Option.default "unit" case.SomaForeign.case_payload then
       native_error "factory argument differs from the declared payload (unit for a nullary tag)";
      SomaForeign.NativeVariantFactory(tag,Some v)
    | SomaForeign.NativeAssertionFunction(line,column) ->
      if argument_names<>["unit"] then native_error "an assertion function needs a unit getter";
      if line<=0 || column<0 then native_error "an assertion location needs a positive line and a nonnegative column";
      (match arguments [] None result with
       | [(_,None)],_ -> ()
       | _ -> native_error "an assertion function needs one positional input");
      SomaForeign.NativeAssertionFunction(line,column)
    | SomaForeign.NativeAssertionFunctionFactory(line,column) ->
      if argument_names<>["unit"] then native_error "an assertion function factory needs a unit getter";
      if line<=0 || column<0 then native_error "an assertion location needs a positive line and a nonnegative column";
      let parameters,_=arguments [] (Some 2) result in
      (match parameters with
       |[(trigger,None);(_,None)] when
          EConstr.isRefX env sigma (Rocqlib.lib_ref "core.unit.type")
            (Reductionops.whd_all env sigma trigger) -> ()
       |_ -> native_error "an assertion function factory has type unit -> input -> answer with positional arguments");
      SomaForeign.NativeAssertionFunctionFactory(line,column)
    | SomaForeign.NativeAssertionFactory(line,column) ->
      if argument_names<>["unit"] then native_error "an assertion factory needs a unit getter";
      if line<=0 || column<0 then native_error "an assertion location needs a positive line and a nonnegative column";
      (* The returned factory creates a closed unit thunk at each source
         creation phase. Neither argument may affect its answer type. *)
      let rec unit_arguments count typ =
        if count=0 then () else
        match EConstr.kind sigma (Reductionops.whd_all env sigma typ) with
        | Prod(binder,domain,codomain)
          when binder.Context.binder_name=Anonymous &&
               EConstr.isRefX env sigma (Rocqlib.lib_ref "core.unit.type") domain &&
               EConstr.Vars.noccurn sigma 1 codomain ->
          unit_arguments (count-1) (EConstr.Vars.subst1 EConstr.mkProp codomain)
        | _ -> native_error "an assertion factory has type unit -> unit -> answer" in
      unit_arguments 2 result;
      SomaForeign.NativeAssertionFactory(line,column)
    | SomaForeign.NativeVariantFunction(tag,_) ->
      if argument_names<>["unit"]then native_error "a variant function needs a unit getter";
      let parameters,answer=arguments [] None result in
      let payload=match parameters with
        |[(payload,None)]->payload
        |_->native_error "a variant function needs one positional payload (unit for a nullary tag)"in
      let v=variant_type ~allow_open:true answer in
      let tag=native_variant_tag tag in
      let case=match List.find_opt(fun c->c.SomaForeign.case_tag=tag)v.variant_cases with
        |Some case->case|None->native_error "function tag is absent from the native variant"in
      if ocaml_type env sigma type_vars payload<>Option.default "unit"case.SomaForeign.case_payload then
        native_error "variant function argument differs from the declared payload";
      SomaForeign.NativeVariantFunction(tag,Some v)
    | SomaForeign.NativeStaticInvocation(expression,_) ->
      if argument_names<>["unit"] then native_error "a static invocation needs a unit getter";
      let inputs,labels,answer=static_shape result in
      if inputs=[] then native_error "a static invocation needs a public function argument";
      let rec closed = function
        | SomaForeign.NativeExternalConstant _ | SomaForeign.NativeFloatConstant _
        | SomaForeign.NativeExternalLiteralConstant _ | SomaForeign.NativeExternalLiteralFunction _
        | SomaForeign.NativeExternalInsertedLiteralFunction _ | SomaForeign.NativeExternalFieldsFunction _
        | SomaForeign.NativeExternalComposedValue _ | SomaForeign.NativeExternalTransformedComposition _
        | SomaForeign.NativeVariantFunction(_,Some _) | SomaForeign.NativeAssertionFunction _ -> true
        | SomaForeign.NativeStaticFunction(_,_,_,Some(a,b,_,_,_)) -> closed a && closed b
        | SomaForeign.NativeStaticApplication(_,_,Some(fn,values,_,_)) -> closed fn && List.for_all closed values
        | SomaForeign.NativeStaticInvocation(_,Some(term,_)) -> closed_term term
        | _ -> false
      and closed_term = function
        | SomaForeign.NativeStaticArgument _ -> true
        | SomaForeign.NativeStaticLambda(body,_) -> closed_term body
        | SomaForeign.NativeStaticValue operation -> closed operation
        | SomaForeign.NativeStaticCall(operation,values,_) -> closed operation && List.for_all closed_term values in
      let descriptor name =
        let operation,typ=static_descriptor name in
        if not(closed operation) then native_error "a static invocation needs closed native value/function getters";
        operation,typ in
      let callable name =
        let c=match Nametab.locate(Libnames.qualid_of_string name)with
          |GlobRef.ConstRef c->c|_->native_error "a static function needs a declared callable type" in
        let count=match Cmap_env.find_opt c !bindings with
          |Some{item=SomaForeign.OCamlNativeCallableType _;_}->0
          |Some{item=SomaForeign.OCamlNativeParametricCallable(params,_);_}->List.length params
          |_->native_error "a static function needs a declared callable type" in
        if count>List.length type_vars then native_error "static function type parameters exceed the public parameters";
        let typ=EConstr.mkApp(EConstr.of_constr(Constr.mkConstU(c,UVars.Instance.empty)),Array.init count(fun index->EConstr.mkRel(List.length type_vars-index)))in
        typ,native_callable_type env sigma type_vars typ in
      let rec check inputs = function
        | SomaForeign.StaticLambda(name,body) ->
          let typ,signature=callable name in
          if signature.SomaForeign.callable_arguments=[] then native_error "a static function needs a callable argument";
          let body,actual=check(inputs @ signature.callable_arguments)body in
          if actual<>signature.callable_result then native_error "a static function result differs from its callable signature";
          SomaForeign.NativeStaticLambda(body,signature),ocaml_type env sigma type_vars typ
        | SomaForeign.StaticArgument index ->
          if index<0 || index>=List.length inputs then native_error "a static argument index exceeds the public arity";
          SomaForeign.NativeStaticArgument index,List.nth inputs index
        | SomaForeign.StaticValue name ->
          let operation,typ=descriptor name in
          SomaForeign.NativeStaticValue operation,ocaml_type env sigma type_vars typ
        | SomaForeign.StaticCall(name,values) ->
          let operation,typ=descriptor name in
          (* Ordinary borrowed arrows may return a partial application. Its
             remaining arrow is checked as a value type. Opaque callable and
             generated function blueprints keep their declared full arity. *)
          let wanted,labels,answer=match operation with
            | SomaForeign.NativeExternalConstant _ ->
              let parameters,rest=arguments [] (Some(List.length values)) typ in
              if parameters=[] then static_shape typ else begin
                let remaining,_=arguments [] None rest in
                if List.exists(fun(_,label)->Option.has_some label)remaining then
                  native_error "a partial static invocation needs a declared callable for a labelled result";
                List.map(fun(t,_)->ocaml_type env sigma type_vars t)parameters,
                List.map snd parameters,ocaml_type env sigma type_vars rest
              end
            | _ -> static_shape typ in
          if wanted=[] || List.length wanted<>List.length values then
            native_error "a static invocation call has the wrong arity";
          let checked=List.map(check inputs)values in
          List.iter2(fun expected(_,actual)->if expected<>actual then
            native_error "a static invocation argument differs from its target domain")wanted checked;
          SomaForeign.NativeStaticCall(operation,List.map fst checked,labels),answer in
      let term,actual=check inputs expression in
      if actual<>answer then native_error "a static invocation result differs from the public signature";
      SomaForeign.NativeStaticInvocation(expression,Some(term,labels))
    | SomaForeign.NativeStaticApplication(target,bound,_) ->
      if argument_names<>["unit"]then native_error "a static application needs a unit getter";
      let rec closed = function
        |SomaForeign.NativeExternalConstant _|SomaForeign.NativeFloatConstant _
        |SomaForeign.NativeExternalLiteralConstant _|SomaForeign.NativeExternalLiteralFunction _
        |SomaForeign.NativeExternalInsertedLiteralFunction _|SomaForeign.NativeExternalFieldsFunction _
        |SomaForeign.NativeExternalComposedValue _|SomaForeign.NativeExternalTransformedComposition _
        |SomaForeign.NativeVariantFunction(_,Some _)->true
        |SomaForeign.NativeStaticFunction(_,_,_,Some(a,b,_,_,_))->closed a && closed b
        |SomaForeign.NativeStaticApplication(_,_,Some(fn,values,_,_))->closed fn && List.for_all closed values
        |_->false in
      let operation,target_type=static_descriptor target in
      let values=List.map static_descriptor bound in
      if not(closed operation && List.for_all(fun(operation,_)->closed operation)values)then
        native_error "a static application needs closed native value/function getters";
      let target_args,target_labels,answer=static_shape target_type in
      if bound=[] || List.length bound>=List.length target_args then
        native_error "a static application binds a nonempty prefix and leaves a public argument";
      let supplied,wanted=CList.chop(List.length bound)target_args in
      List.iter2(fun expected(_,typ)->if expected<>ocaml_type env sigma type_vars typ then
        native_error "a static application bound value differs from its target argument")supplied values;
      let output,labels,result=static_shape result in
      if output<>wanted || result<>answer then
        native_error "static application arguments/result differ from the declared signature";
      SomaForeign.NativeStaticApplication(target,bound,Some(operation,List.map fst values,target_labels,labels))
    | (SomaForeign.NativeStaticFunction(_,outer,inner,_)
      |SomaForeign.NativeStaticCompositionScope(outer,inner,_) as operation) ->
      let scoped=match operation with SomaForeign.NativeStaticCompositionScope _->true|_->false in
      let prefix=if scoped then false else match operation with SomaForeign.NativeStaticFunction(prefix,_,_,_)->prefix|_->false in
      if argument_names<>["unit"] then native_error "a static function needs a unit getter";
      let rec static_operation = function
        |SomaForeign.NativeExternalConstant _|SomaForeign.NativeExternalLiteralFunction _
        |SomaForeign.NativeExternalInsertedLiteralFunction _|SomaForeign.NativeExternalFieldsFunction _
        |SomaForeign.NativeExternalComposedValue _|SomaForeign.NativeExternalTransformedComposition _->true
        |SomaForeign.NativeStaticFunction(_,_,_,Some(a,b,_,_,_))->static_operation a && static_operation b
        |SomaForeign.NativeFloatConstant _->true
        |_->false in
      let left,left_type=static_descriptor outer and right,right_type=static_descriptor inner in
      if not(static_operation left && static_operation right)then
        native_error "a static function only combines closed native value/function getters";
      let left_args,left_labels,left_result=static_shape left_type in
      if left_args=[] then native_error "a static outer input needs a function";
      let wanted,inner_labels = if prefix then begin
        (match right with SomaForeign.NativeExternalConstant _|SomaForeign.NativeFloatConstant _->()
          |_->native_error "a static prefix needs a native value, without creation-time calls");
        if ocaml_type env sigma type_vars right_type<>List.hd left_args then
          native_error "a static prefix differs from the first target argument";
        List.tl left_args,[]
      end else begin
        let inner_args,inner_labels,inner_result=static_shape right_type in
        if inner_args=[] then native_error "a static composition needs an inner function";
        if inner_result<>List.hd left_args then native_error "static inner result differs from the first target argument";
        inner_args @ List.tl left_args,inner_labels
      end in
      let output_type=if scoped then begin
        let head,parts=EConstr.decompose_app sigma(Reductionops.whd_all env sigma result)in
        if Array.length parts<>2 || not(EConstr.isRefX env sigma(Rocqlib.lib_ref "core.prod.type")head)then
          native_error "a static composition scope returns (inner function * composed function)";
        if ocaml_type env sigma type_vars parts.(0)<>ocaml_type env sigma type_vars right_type then
          native_error "the first scope export differs from the inner function type";
        parts.(1)
      end else result in
      let output,labels,answer=static_shape output_type in
      if wanted=[] || output<>wanted || answer<>left_result then
        native_error "static function arguments/result differ from the declared signature";
      let data=Some(left,right,left_labels,inner_labels,labels)in
      if scoped then SomaForeign.NativeStaticCompositionScope(outer,inner,data)
      else SomaForeign.NativeStaticFunction(prefix,outer,inner,data)
    | SomaForeign.NativeExternalInsertedLiteralFunction(path,literal,after,_) ->
      if argument_names<>["unit"] then native_error "a full literal function needs a unit getter";
      let parameters,_=arguments [] None result in
      if parameters=[] || List.exists(fun(_,label)->Option.has_some label)parameters then
        native_error "a full literal function needs positional function arguments";
      if after<0 || after>List.length parameters then native_error "literal position exceeds the function arity";
      SomaForeign.NativeExternalInsertedLiteralFunction(native_external_path path,literal,after,List.length parameters)
    | SomaForeign.NativeExternalFieldsFunction(path,fields,_,_) ->
      if argument_names<>["unit"] then native_error "a full field function needs a unit getter";
      let parameters,_=arguments [] None result in
      if parameters=[] || List.exists(fun(_,label)->Option.has_some label)parameters then
        native_error "a full field function needs positional function arguments";
      let receiver=fst(List.hd parameters) in
      record_type receiver;
      if fields=[] then native_error "a full field function needs a nonempty field path";
      SomaForeign.NativeExternalFieldsFunction(native_external_path path,List.map native_path fields,
        ocaml_type env sigma type_vars receiver,List.length parameters)
    | SomaForeign.NativeExternalLiteralFunction(path,literal,_) ->
      if argument_names<>["unit"] then native_error "a full literal function needs a unit getter";
      let parameters,_=arguments [] None result in
      if parameters=[] || List.exists(fun(_,label)->Option.has_some label)parameters then
        native_error "a full literal function needs positional function arguments";
      SomaForeign.NativeExternalLiteralFunction(native_external_path path,literal,List.length parameters)
    | SomaForeign.NativeFloatConstant literal ->
      if argument_names<>["unit"] || result_name<>"float" then
        native_error "a native float literal needs a unit getter with native float result";
      SomaForeign.NativeFloatConstant literal
    | SomaForeign.NativeCallableApplyFunction _ ->
      if argument_names<>["unit"] then native_error "Apply AsFunction is a unit getter";
      let receiver,_=arguments [] (Some 1) result in
      let receiver=match receiver with [value,None]->value
        |_->native_error "Apply AsFunction returns a positional callable invoker" in
      let callable=native_callable_type env sigma type_vars receiver in
      let parameters,answer=arguments [] (Some(1+List.length callable.SomaForeign.callable_arguments)) result in
      let types=List.map(fun(typ,label)->
        if Option.has_some label then native_error "Apply AsFunction parameters are positional";
        ocaml_type env sigma type_vars typ)(List.tl parameters) in
      if types<>callable.callable_arguments || ocaml_type env sigma type_vars answer<>callable.callable_result then
        native_error "Apply AsFunction signature differs from the declared callable";
      SomaForeign.NativeCallableApplyFunction(Some callable)
    | SomaForeign.NativeCallableApply _ ->
      let c=native_callable_type env sigma type_vars(List.hd args_types)in
      if List.tl argument_names<>c.SomaForeign.callable_arguments || result_name<>c.callable_result then
        native_error "Apply signature differs from the declared callable";
      SomaForeign.NativeCallableApply(Some c)
    | SomaForeign.NativeCallableWrapFull _ ->
      let callable = native_callable_type ~required:"Wrap AtFullApplication needs a declared native callable as its result"
          env sigma type_vars result in
      let parameters, answer =
        arguments [] (Some (List.length callable.SomaForeign.callable_arguments)) (List.hd args_types) in
      let types = List.map (fun (typ, label) ->
          if Option.has_some label then native_error "Wrap AtFullApplication takes a positional function";
          ocaml_type env sigma type_vars typ) parameters in
      if types <> callable.callable_arguments ||
         ocaml_type env sigma type_vars answer <> callable.callable_result then
        native_error "Wrap AtFullApplication input disagrees with the callable signature";
      SomaForeign.NativeCallableWrapFull (Some callable)
    | SomaForeign.NativeCallableWrap _ ->
      let callable = native_callable_type ~required:"Wrap needs a declared native callable as its result"
          env sigma type_vars result in
      let mismatch () = native_error "Wrap input must be a positional callback chain matching the declared callable" in
      let rec check arguments callback =
        match arguments with
        | [] -> if ocaml_type env sigma type_vars callback <> callable.SomaForeign.callable_result then mismatch ()
        | argument :: rest ->
          let head, parts = EConstr.decompose_app sigma (Reductionops.whd_all env sigma callback) in
          if Array.length parts <> 2 || not (EConstr.isRefX env sigma
            (Rocqlib.lib_ref "soma.native.callback") head) ||
            ocaml_type env sigma type_vars parts.(0) <> argument then mismatch ();
          check rest parts.(1)
      in
      check callable.SomaForeign.callable_arguments (List.hd args_types);
      SomaForeign.NativeCallableWrap (Some callable)
    | SomaForeign.NativeValue path -> SomaForeign.NativeValue (native_path path)
    | SomaForeign.NativeExternalValue path -> SomaForeign.NativeExternalValue (native_external_path path)
    | SomaForeign.NativePrimitive (byte, native, noalloc) ->
      let name = ocaml_name ~definition:"native primitive" (Id.to_string name) in
      if not (String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true | _ -> false) name) then
        native_error "a primitive needs an OCaml value identifier";
      if type_parameters <> [] then native_error "primitive signatures must be monomorphic";
      if List.length args > 5 && (native = None || native = Some byte) then
        native_error "a primitive with more than five arguments needs a separate native symbol";
      SomaForeign.NativePrimitive (primitive_symbol byte, Option.map primitive_symbol native, noalloc)
    | SomaForeign.NativeExternalLiteralCallback (path, literal, after) ->
      if after < 0 || after > List.length args then
        native_error "literal insertion position must be between zero and the native argument count";
      SomaForeign.NativeExternalLiteralCallback (native_external_path path, literal, after)
    | SomaForeign.NativeExternalConstant path ->
      if argument_names<>["unit"]then native_error "an external value getter takes unit";
      SomaForeign.NativeExternalConstant(native_external_path path)
    | SomaForeign.NativeExternalLiteralConstant (path, literal) ->
      if argument_names<>["unit"]then native_error "an external value getter takes unit";
      SomaForeign.NativeExternalLiteralConstant(native_external_path path, literal)
    | (SomaForeign.NativeExternalComposedValue (outer, inner, after, _)
      | SomaForeign.NativeExternalTransformedComposition (outer, inner, after, _, _, _)) as composition ->
      if argument_names <> ["unit"] then native_error "a composed external value getter takes unit";
      let rec arity typ =
        match EConstr.kind sigma (Reductionops.whd_all env sigma typ) with
        | Prod (binder, domain, codomain) ->
          if binder.Context.binder_name <> Anonymous || is_sort env sigma domain ||
             not (EConstr.Vars.noccurn sigma 1 codomain) then
            native_error "a composed value returns a positional non-dependent function";
          1 + arity (EConstr.Vars.subst1 (EConstr.mkProp) codomain)
        | _ -> 0 in
      let count = arity result in
      if after < 0 || after >= count then
        native_error "composition split must leave at least one inner argument";
      let outer = native_external_path outer and inner = native_external_path inner in
      (match composition with
       | SomaForeign.NativeExternalTransformedComposition (_, _, _, _, transform, position) ->
         if position < 0 || position >= count then
           native_error "composition transform position must select an argument";
         SomaForeign.NativeExternalTransformedComposition
           (outer, inner, after, count, native_external_path transform, position)
       | _ -> SomaForeign.NativeExternalComposedValue (outer, inner, after, count))
    | SomaForeign.NativeExternalException path ->
      if argument_names<>["unit"] ||
         not (EConstr.isRefX env sigma (Rocqlib.lib_ref "soma.exception_value.type") result) then
        native_error "an external exception getter takes unit and returns an exception";
      SomaForeign.NativeExternalException(native_constructor_path path)
    | SomaForeign.NativeVariantView _ ->
      if List.length args<>1 then native_error "View needs one native variant argument";
      let v=variant_type(List.hd args_types)in
      if result_name<>SomaForeign.native_variant_view_type v then
        native_error "View result must be the ordered nested result of its payloads (unit for nullary tags)";
      SomaForeign.NativeVariantView(Some v)
    | SomaForeign.NativeVariantBuild(tag,_) ->
      if List.length args<>1 then native_error "Construct needs one payload argument (unit for a nullary tag)";
      let v=variant_type ~allow_open:true result in
      let tag=native_variant_tag tag in
      let case=match List.find_opt(fun c->c.SomaForeign.case_tag=tag)v.variant_cases with
        | Some c->c|None->native_error "Construct tag is absent from the native variant" in
      if List.hd argument_names<>Option.default "unit" case.SomaForeign.case_payload then
        native_error "Construct argument differs from the declared payload (unit for a nullary tag)";
      SomaForeign.NativeVariantBuild(tag,Some v)
    | SomaForeign.NativeConstructorTag(path,arity) ->
      if not(EConstr.isRefX env sigma(Rocqlib.lib_ref "core.bool.type")result)then
       native_error "Tag result must be bool";
      SomaForeign.NativeConstructorTag(native_constructor_path path,arity)
    | SomaForeign.NativeConstructorCase(path,arity) ->
      let head,payload=EConstr.decompose_app sigma(Reductionops.whd_all env sigma result)in
      if Array.length payload<>1 || not(EConstr.isRefX env sigma(Rocqlib.lib_ref "core.option.type")head)then
       native_error "Case result must be option payload";
      if arity=0 && not(EConstr.isRefX env sigma(Rocqlib.lib_ref "core.unit.type")payload.(0))then
       native_error "a nullary Case payload must be unit";
      SomaForeign.NativeConstructorCase(native_constructor_path path,arity)
    | SomaForeign.NativeConstructorBuild(path,arity) ->
      if arity=0 then begin
        if argument_names<>["unit"] then native_error "a nullary Constructor takes unit"
      end else if List.length args<>arity then
        native_error "constructor arity and argument count differ";
      SomaForeign.NativeConstructorBuild(native_constructor_path path,arity)
    | SomaForeign.NativeInlineGet (path, label) ->
      let head, args = EConstr.decompose_app sigma (Reductionops.whd_all env sigma result) in
      if Array.length args <> 1 || not (EConstr.isRefX env sigma (Rocqlib.lib_ref "core.option.type") head) then
        native_error "Inline Get result must be option";
      SomaForeign.NativeInlineGet (native_constructor_path path, field label)
    | SomaForeign.NativeInlineSet (path, label) ->
      if result_name <> "bool" then native_error "Inline Set result must be bool";
      SomaForeign.NativeInlineSet (native_constructor_path path, field label)
    | SomaForeign.NativeInlineBuild (path, fields) ->
      if List.length args <> List.length fields then
        native_error "inline record field and argument counts differ";
      if List.length (List.sort_uniq String.compare fields) <> List.length fields then
        native_error "inline record fields must be distinct";
      SomaForeign.NativeInlineBuild (native_constructor_path path, List.map field fields)
    | SomaForeign.NativeBoundBooleanFunction (path, callable, label, value) ->
      if argument_names<>["unit"] then native_error "a bound function takes a unit getter";
      let bound=List.filter_map(fun(typ,name)->
        if name=Some label then Some typ else None)
        (List.combine callable.SomaForeign.callable_arguments callable.callable_labels)in
      if bound<>["bool"] then
        native_error "a bound boolean function needs one required bool label from its callable";
      let required=List.filter_map(fun(typ,name)->match name with
        |Some name when name=label || String.starts_with ~prefix:"?" name->None
        |_->Some typ)
        (List.combine callable.SomaForeign.callable_arguments callable.callable_labels)in
      if required=[] then native_error "a bound function needs a remaining required argument";
      let parameters,answer=arguments [] (Some(List.length required))result in
      if List.exists(fun(_,label)->Option.has_some label)parameters ||
         List.map(fun(typ,_)->ocaml_type env sigma type_vars typ)parameters<>required ||
         ocaml_type env sigma type_vars answer<>callable.callable_result then
        native_error "bound function signature differs from the remaining required callable arguments";
      SomaForeign.NativeBoundBooleanFunction(native_path path,callable,label,value)
    | SomaForeign.NativeDefaultedFunction (path, callable) ->
      if argument_names<>["unit"] then native_error "a defaulted function takes a unit getter";
      let required=List.filter_map(fun(typ,label)->match label with
        |Some label when String.starts_with ~prefix:"?" label->None|_->Some typ)
        (List.combine callable.SomaForeign.callable_arguments callable.callable_labels)in
      if required=[] then native_error "a defaulted function needs a required argument";
      let parameters,answer=arguments [] (Some(List.length required))result in
      if List.exists(fun(_,label)->Option.has_some label)parameters ||
         List.map(fun(typ,_)->ocaml_type env sigma type_vars typ)parameters<>required ||
         ocaml_type env sigma type_vars answer<>callable.callable_result then
        native_error "defaulted function signature differs from the required callable arguments";
      SomaForeign.NativeDefaultedFunction(native_path path,callable)
    | SomaForeign.NativeDeferredFields (fields, _) ->
      if argument_names<>["unit"] then native_error "a deferred field getter takes unit";
      let parameters, _value = arguments [] (Some 2) result in
      let receiver, trigger = match parameters with
        | [receiver,None;trigger,None] -> receiver,trigger
        | _ -> native_error "a deferred field getter returns record -> unit -> value" in
      record_type receiver;
      if not (EConstr.isRefX env sigma (Rocqlib.lib_ref "core.unit.type")
        (Reductionops.whd_all env sigma trigger)) then
        native_error "a deferred field getter is triggered by unit";
      if fields=[] then native_error "a deferred field getter needs a nonempty field path";
      SomaForeign.NativeDeferredFields(List.map native_path fields,ocaml_type env sigma type_vars receiver)
    | SomaForeign.NativeGetFunction (name, _) ->
      if argument_names <> ["unit"] then native_error "a record getter takes unit";
      let parameters, value = arguments [] (Some 1) result in
      let receiver = match parameters with
        | [receiver, None] -> receiver
        | _ -> native_error "a record getter returns a positional selector" in
      let name, declaration, local = owned_record_field "record getter" receiver name in
      if local (ocaml_type env sigma type_vars value) <> declaration.SomaForeign.field_type then
        native_error "record getter result disagrees with its field type";
      SomaForeign.NativeGetFunction (name, ocaml_type env sigma type_vars receiver)
    | SomaForeign.NativeSetFunction (name, _) ->
      if argument_names <> ["unit"] then native_error "a record setter takes unit";
      let parameters, completion = arguments [] (Some 2) result in
      let receiver, value = match parameters with
        | [receiver, None; value, None] -> receiver, value
        | _ -> native_error "a record setter returns a positional record -> value -> unit function" in
      if not (EConstr.isRefX env sigma (Rocqlib.lib_ref "core.unit.type") completion) then
        native_error "a record setter must return unit";
      let name, declaration, local = owned_record_field "record setter" receiver name in
      if not declaration.SomaForeign.field_mutable then
        native_error "a record setter requires a mutable field";
      if local (ocaml_type env sigma type_vars value) <> declaration.SomaForeign.field_type then
        native_error "record setter argument disagrees with its field type";
      SomaForeign.NativeSetFunction (name, ocaml_type env sigma type_vars receiver)
    | SomaForeign.NativeGet f ->
      if List.length args<>1 then native_error "Get needs one record argument";
      SomaForeign.NativeGet(field f)
    | SomaForeign.NativeSet f ->
      if List.length args<>2 || result_name<>"unit" then native_error "Set needs record -> value -> unit";
      SomaForeign.NativeSet(field f)
    | SomaForeign.NativeBuildEvaluating (fields, evaluated) ->
      if List.length args <> List.length fields then
        native_error "record field and argument counts differ";
      if List.length (List.sort_uniq String.compare fields) <> List.length fields ||
         List.length (List.sort_uniq String.compare evaluated) <> List.length evaluated then
        native_error "record fields must be distinct";
      List.iter (fun name ->
        if not (List.mem name fields) then native_error "an evaluated field must be part of the record") evaluated;
      List.iter2 (fun name typ ->
        if List.mem name evaluated then
          match EConstr.kind sigma (Reductionops.whd_all env sigma typ) with
          | Prod (_, argument, _) when EConstr.isRefX env sigma (Rocqlib.lib_ref "core.unit.type") argument -> ()
          | _ -> native_error "an evaluated field needs a unit thunk") fields args_types;
      SomaForeign.NativeBuildEvaluating (List.map field fields, evaluated)
    | SomaForeign.NativeRecordFactory (fields, reading, _) ->
      if argument_names <> ["unit"] then native_error "a record factory getter takes unit";
      let distinct names = List.length (List.sort_uniq String.compare names) = List.length names in
      if not (distinct fields && distinct reading) then native_error "record factory fields must be distinct";
      if not (List.for_all (fun name -> List.mem name fields) reading) then
        native_error "a reference read must name a factory record field";
      let rec check parameters typ =
        match parameters, EConstr.kind sigma (Reductionops.whd_all env sigma typ) with
        | name :: tail, Prod (binder, domain, codomain) ->
          if binder.Context.binder_name <> Anonymous || is_sort env sigma domain ||
             not (EConstr.Vars.noccurn sigma 1 codomain) then
            native_error "a record factory returns a positional non-dependent function";
          if List.mem name reading then begin
            let head, args = EConstr.decompose_app sigma (Reductionops.whd_all env sigma domain) in
            if Array.length args <> 1 ||
               not (EConstr.isRefX env sigma (Rocqlib.lib_ref "soma.reference.type") head) then
              native_error "a record factory read needs a reference argument"
          end;
          check tail (EConstr.Vars.subst1 (EConstr.mkProp) codomain)
        | [], Prod _ -> native_error "record factory field and argument counts differ"
        | [], _ -> record_type typ; ocaml_type env sigma type_vars typ
        | _ -> native_error "record factory field and argument counts differ" in
      let owner = check fields result in
      SomaForeign.NativeRecordFactory (List.map field fields, reading, owner)
    | SomaForeign.NativeVariantDispatch (cases, _, with_context) ->
      if argument_names <> ["unit"] then native_error "a variant dispatch getter takes unit";
      let arity = List.length cases + if with_context then 2 else 1 in
      let parameters, terminal = arguments [] (Some arity) result in
      let receiver, context, handlers = match with_context, List.rev parameters with
        | true, (receiver, None) :: (context, None) :: handlers
          when List.length handlers = List.length cases ->
          receiver, Some (ocaml_type env sigma type_vars context), List.rev handlers
        | false, (receiver, None) :: handlers when List.length handlers = List.length cases ->
          receiver, None, List.rev handlers
        | _ -> native_error "variant dispatch takes one handler per case, then its context (if declared) and variant value" in
      let head, type_args = EConstr.decompose_app sigma receiver in
      let group, member = match EConstr.kind sigma head with
        | Const (c, _) ->
          (match Cmap_env.find_opt c !bindings with
           | Some { item = SomaForeign.OCamlNativeAlgebraic (group, member); _ }
             when Array.length type_args = 0 -> group, member
           | _ -> native_error "variant dispatch needs a declared native algebraic variant")
        | _ -> native_error "variant dispatch needs a declared native algebraic variant" in
      let constructors = match List.assoc member group.SomaForeign.algebraic_members with
        | SomaForeign.Algebraic_variant constructors -> constructors
        | SomaForeign.Algebraic_record _ ->
          native_error "variant dispatch needs a declared native algebraic variant" in
      let sorted = List.sort String.compare in
      if sorted (List.map (fun (constructor, _, _) -> constructor) cases) <>
         sorted (List.map fst constructors) then
        native_error "variant dispatch must cover every constructor once";
      let owner = ocaml_type env sigma type_vars receiver in
      let local = local_record_type (SomaForeign.native_algebraic_module group ^ ".") in
      let result = ocaml_type env sigma type_vars terminal in
      let validate (constructor, pattern, keep_receiver) (handler, label) =
        if Option.has_some label then native_error "variant dispatch handlers are positional";
        let expected, pattern = match pattern, List.assoc constructor constructors with
          | SomaForeign.Dispatch_arguments _, SomaForeign.Constructor_arguments arguments ->
            arguments, SomaForeign.Dispatch_arguments (List.length arguments)
          | SomaForeign.Dispatch_fields names, SomaForeign.Constructor_record fields ->
            if List.length (List.sort_uniq String.compare names) <> List.length names then
              native_error "variant dispatch fields must be distinct";
            let field_type name = match List.find_opt (fun f -> f.SomaForeign.field_name = name) fields with
              | Some field -> field.SomaForeign.field_type
              | None -> native_error "variant dispatch field is absent from its constructor" in
            List.map field_type names, SomaForeign.Dispatch_fields names
          | SomaForeign.Dispatch_ignore _, SomaForeign.Constructor_arguments arguments ->
            [], SomaForeign.Dispatch_ignore (arguments <> [])
          | SomaForeign.Dispatch_ignore _, SomaForeign.Constructor_record _ ->
            [], SomaForeign.Dispatch_ignore true
          | _ -> native_error "variant dispatch pattern disagrees with the declared constructor" in
        let expected = if keep_receiver then owner :: expected else expected in
        let expected = if expected = [] then ["unit"] else expected in
        let expected = match context with Some typ -> typ :: expected | None -> expected in
        let parameters, answer = arguments [] (Some (List.length expected)) handler in
        let types = List.map (fun (typ, label) ->
            if Option.has_some label then native_error "variant dispatch callback parameters are positional";
            ocaml_type env sigma type_vars typ) parameters in
        if List.map local types <> List.map local expected ||
           ocaml_type env sigma type_vars answer <> result then
          native_error ("variant dispatch handler disagrees with its payload or result: " ^ constructor);
        constructor, pattern, keep_receiver in
      SomaForeign.NativeVariantDispatch (List.map2 validate cases handlers, owner, with_context)
    | SomaForeign.NativeBuild fields | SomaForeign.NativeCopy fields as op ->
      let expected = List.length fields + (match op with SomaForeign.NativeCopy _ -> 1 | _ -> 0) in
      if List.length args<>expected then native_error "record field and argument counts differ";
      if List.length(List.sort_uniq String.compare fields)<>List.length fields then native_error "record fields must be distinct";
      List.iter(fun f->ignore(field f))fields;op in
  (match operation with
    | SomaForeign.NativeValue _ | SomaForeign.NativeExternalValue _ | SomaForeign.NativeExternalLiteralCallback _ -> () | _ ->
    if List.exists Option.has_some labels then native_error "native data callback arguments are positional");
  let ast t = Constrextern.extern_constr ~flags:(PrintingFlags.current ()) env sigma t in
  let rec product = function
    | [t] -> ast t
    | t::rest -> native_app (native_global "core.prod.type") [ast t;product rest]
    | [] -> assert false in
  let descriptor_type = native_app (native_global "soma.native.callback") [product args_types;ast result] in
  let namespace = native_namespace () in
  let body = native_app
    (CAst.make(Constrexpr.CRef(Libnames.qualid_of_string "Soma.Native.Named_callback",None)))
    [native_string namespace;native_string(Id.to_string name)] in
  let body=if type_parameters=[]then body else CAst.make(Constrexpr.CLambdaN(type_parameters,body))in
  let descriptor_type=if type_parameters=[]then descriptor_type else CAst.make(Constrexpr.CProdN(type_parameters,descriptor_type))in
  let c = native_declare name body (Some descriptor_type) in
  native_register name c (SomaForeign.OCamlNativeCallback {
    namespace;name=Id.to_string name;arguments=argument_names;result=result_name;labels;operation})

let native_getter name result operation =
  let open Constrexpr in
  let unit_argument = CLocalAssum ([CAst.make Anonymous], None,
    Default Glob_term.Explicit, native_global "core.unit.type") in
  (* Type parameters belong to the descriptor, not to the returned value.
     Keep the native unit getter below them so extraction erases those binders
     at the call site, as for a polymorphic External Callback. *)
  let rec insert_unit result =
    match result.CAst.v with
    | CProdN ((CLocalAssum (_, _, _, domain) as binder) :: rest, body)
      when Constrexpr_ops.isCSort domain ->
      let body = if rest = [] then body else CAst.make (CProdN (rest, body)) in
      CAst.make (CProdN ([binder], insert_unit body))
    | _ -> CAst.make (CProdN ([unit_argument], result))
  in
  native_callback name (insert_unit result) operation

(* Literal data has a native static representation, without a new logical
   float assumption or a runtime parser/allocation. Canonicalization also
   keeps spelling out of the ABI and rejects non-finite/code-like input. *)
let native_float_constant name result literal =
  if literal="" || not(String.for_all(function '0'..'9'|'.'|'e'|'E'|'+'|'-'->true|_->false)literal) then
    native_error "a native float literal needs a finite decimal numeral";
  let value=try float_of_string literal with Failure _->
    native_error "a native float literal needs a finite decimal numeral" in
  if not(Float.is_finite value) then native_error "a native float literal must be finite";
  let literal=Printf.sprintf "%.17g" value in
  let literal=if String.exists(function '.'|'e'|'E'->true|_->false)literal then literal else literal^"." in
  native_getter name result (SomaForeign.NativeFloatConstant literal)

let native_static_composition_scope name result outer inner =
  native_getter name result (SomaForeign.NativeStaticCompositionScope(Id.to_string outer,Id.to_string inner,None))

let native_static_invocation name result target arguments =
  native_getter name result (SomaForeign.NativeStaticInvocation(
    SomaForeign.StaticCall(Id.to_string target,arguments),None))

let native_static_application name result target bound =
  native_getter name result (SomaForeign.NativeStaticApplication(Id.to_string target,List.map Id.to_string bound,None))

let native_variant_function name result tag =
  native_getter name result (SomaForeign.NativeVariantFunction(tag,None))

let native_static_function name result prefix outer inner =
  native_getter name result (SomaForeign.NativeStaticFunction(prefix,Id.to_string outer,Id.to_string inner,None))

let native_inserted_literal_function name result path literal after =
  native_getter name result (SomaForeign.NativeExternalInsertedLiteralFunction(path,literal,after,0))

let native_fields_function name result path fields =
  native_getter name result (SomaForeign.NativeExternalFieldsFunction(path,fields,"",0))

let native_literal_function name result path literal =
  native_getter name result (SomaForeign.NativeExternalLiteralFunction(path,literal,0))

(* Keep the failure expression closed inside its original creation phase.
   OCaml can therefore share it natively and allocate it freshly in bytecode,
   just as a source-level [fun () -> assert false] argument. *)
let native_assertion_factory name result line column =
  native_getter name result (SomaForeign.NativeAssertionFactory(line,column))

let native_assertion_function_factory name result line column =
  native_getter name result (SomaForeign.NativeAssertionFunctionFactory(line,column))

let native_external_thunk_factory name result path literal =
  native_getter name result (SomaForeign.NativeExternalThunkFactory(path,literal))

let native_variant_factory name result tag =
  native_getter name result (SomaForeign.NativeVariantFactory(tag,None))

let native_apply_function name result =
  native_getter name result (SomaForeign.NativeCallableApplyFunction None)

let native_defaulted_function name result path schema =
  ignore(native_context());
  let env=Global.env()in
  let sigma,schema=Constrintern.interp_type_evars env (Evd.from_env env) schema in
  let callable=native_callable_type env sigma [] schema in
  native_getter name result (SomaForeign.NativeDefaultedFunction(path,callable))

let native_bound_boolean_function name result path schema label value =
  ignore(native_context());
  let env=Global.env()in
  let sigma,schema=Constrintern.interp_type_evars env (Evd.from_env env) schema in
  let callable=native_callable_type env sigma [] schema in
  native_getter name result (SomaForeign.NativeBoundBooleanFunction(path,callable,label,value))

let native_deferred_fields name result fields =
  native_getter name result (SomaForeign.NativeDeferredFields(fields,""))

let native_get_function name result field =
  native_getter name result (SomaForeign.NativeGetFunction (field, ""))

let native_set_function name result field =
  native_getter name result (SomaForeign.NativeSetFunction (field, ""))

let native_variant_dispatch name result cases with_context =
  native_getter name result (SomaForeign.NativeVariantDispatch (cases, "", with_context))

let native_record_factory name result fields reading =
  native_getter name result (SomaForeign.NativeRecordFactory (fields, reading, ""))

let native_external_constant ?literal name result path =
  let operation = match literal with
    | None -> SomaForeign.NativeExternalConstant path
    | Some literal -> SomaForeign.NativeExternalLiteralConstant (path, literal) in
  native_getter name result operation

let native_composed_value name result outer inner after =
  native_getter name result (SomaForeign.NativeExternalComposedValue (outer, inner, after, 0))

let native_transformed_composition name result outer inner after transform position =
  native_getter name result
    (SomaForeign.NativeExternalTransformedComposition (outer, inner, after, 0, transform, position))

let native_external_exception name path =
  native_getter name (native_global "soma.exception_value.type")
    (SomaForeign.NativeExternalException path)

(* [OCaml Bind "FILE.ml"]: FILE.definition declares FILE.ml *)
let bind file =
  let base = Filename.basename file in
  (* a project's FILE.ml is kept relative to its root, and found in the
     checkout being built (vernac/somaImport.ml) *)
  let file = SomaImport.project_file file in
  bind_module ~key:file ~ml_file:(Some file) ~top:(module_name file)
    ~definition:(Filename.remove_extension base ^ ".definition")

(* [OCaml Bind C "FILE.c"]: FILE.definition declares FILE.c, whose OCaml
   module Soma generates (vernac/somaC.ml): what C can take is narrower
   than what OCaml can, and said here, where the definition is compiled *)
let bind_c file =
  let base = Filename.basename file in
  let definition = Filename.remove_extension base ^ ".definition" in
  let file = SomaImport.project_file file in
  let top = module_name file in
  if !pending <> [] then
    CErrors.user_err (str definition ++ str ": a C module uses no OCaml library (OCaml Library).");
  bind_module ~key:file ~ml_file:(Some file) ~top ~definition;
  Cmap_env.iter (fun _ b ->
      if String.equal b.key file then begin
        if String.contains b.path '.' then
          CErrors.user_err (str definition ++ str ": " ++ str b.path ++
                            str " is in a module; a C module's declarations are at its top, each the C function " ++
                            str (SomaC.base_of base) ++ str "_name.");
        match b.item with
        | SomaForeign.OCamlNativeModuleAlias _ | SomaForeign.OCamlNativeOpenVariant _ | SomaForeign.OCamlNativeParametricCallable _ | SomaForeign.OCamlNativeParametricVariant _ | SomaForeign.OCamlNativeExternalFamily _ | SomaForeign.OCamlNativeImmutableRecord _ | SomaForeign.OCamlNativeType _ | SomaForeign.OCamlNativeAlgebraic _ | SomaForeign.OCamlNativeOwnedRecord _ | SomaForeign.OCamlNativeOwnedVariant _ | SomaForeign.OCamlNativeCallableType _ | SomaForeign.OCamlNativeCallback _ ->
          CErrors.user_err (str "native declarations cannot be bound to C")
        | SomaForeign.OCamlType 0 -> ()
        | SomaForeign.OCamlType _ ->
          CErrors.user_err (str definition ++ str ": " ++ str b.path ++
                            str " has parameters; a C module's types are handles (name : Type.), with none.")
        | SomaForeign.OCamlValue (ty, _) ->
          match SomaC.signature ~top ty with
          | Ok _ -> ()
          | Error why ->
            CErrors.user_err (hov 0 (str definition ++ str ": " ++ str b.path ++ str " : " ++ str ty ++
                                     str " is not given to C:" ++ spc () ++ str why ++ str "."))
      end) !bindings

(* [OCaml Bind Module "Async"]: async.definition, next to no module,
   declares a library's module *)
let bind_library top =
  if not (is_module_name top) || top.[0] <> Char.uppercase_ascii top.[0] then
    CErrors.user_err (str top ++ str " is no name of an OCaml module.");
  bind_module ~key:top ~ml_file:None ~top ~definition:(String.uncapitalize_ascii top ^ ".definition")

(* * What other parts of Soma see *)

let ocaml_modules () =
  CString.Map.fold (fun key (ml_file, top, libraries) acc ->
      let items = Cmap_env.fold (fun c b acc ->
          if String.equal b.key key then (c, b.path, b.item) :: acc else acc) !bindings [] in
      let ml_file = Option.map SomaImport.resolve_project_file ml_file in
      { SomaForeign.ml_file; top; libraries; items = List.rev items } :: acc)
    !modules []

let describe c =
  match Cmap_env.find_opt c !bindings with
  | None -> None
  | Some b ->
    let whose = match CString.Map.find_opt b.key !modules with
      | Some (Some file, _, _) -> str (Filename.basename file) ++ str "'s "
      | _ when String.equal b.top "Soma_host" -> str "Soma.Host's primitive, "
      | _ -> str "OCaml's " in
    let path = b.top ^ "." ^ b.path in
    Some (match b.item with
        | SomaForeign.OCamlNativeModuleAlias info ->
          str "native module alias " ++ str info.module_alias_namespace ++ str "." ++
          str info.module_alias_name ++ str " = " ++ str info.module_alias_target
        | SomaForeign.OCamlNativeCallableType c | SomaForeign.OCamlNativeParametricCallable(_,c) ->
          str "native callable " ++ str(SomaForeign.native_callable_type c) ++ str ", opaque to Soma"
        | SomaForeign.OCamlNativeOpenVariant(row,v) ->
          str "open native variant " ++ str(row^" "^SomaForeign.native_variant_type v)
        | SomaForeign.OCamlNativeParametricVariant(_,v) ->
          str "parameterized closed native variant " ++ str(SomaForeign.native_variant_type v)
        | SomaForeign.OCamlNativeOwnedVariant v ->
          str "closed native polymorphic variant " ++ str(SomaForeign.native_variant_type v) ++ str ", opaque to Soma"
        | SomaForeign.OCamlNativeImmutableRecord(r,_) ->
          str "immutable native record " ++ str(SomaForeign.native_record_type r) ++ str ", with a structural logical model"
        | SomaForeign.OCamlNativeOwnedRecord r ->
          str "owned native record " ++ str(SomaForeign.native_record_type r) ++ str ", opaque to Soma"
        | SomaForeign.OCamlNativeAlgebraic (group, member) ->
          str "native algebraic type " ++ str (SomaForeign.native_algebraic_type group member)
        | SomaForeign.OCamlNativeExternalFamily (_, path) ->
          str "native opaque type family " ++ str path ++ str ", with no logical evaluator"
        | SomaForeign.OCamlNativeType path ->
          str "native opaque type " ++ str path ++ str ", with no logical evaluator"
        | SomaForeign.OCamlNativeCallback n ->
          str "native callback " ++ str n.namespace ++ str "." ++ str n.name ++
          str ", checked by OCaml, with no logical evaluator"
        | SomaForeign.OCamlType _ ->
          whose ++ str "type " ++ str path ++ str ", opaque to Soma"
        | SomaForeign.OCamlValue (ty, labels) ->
          let labeled = List.filter_map Fun.id labels in
          whose ++ str path ++ str " : " ++ str ty ++
          (if labeled = [] then mt () else
             str " (" ++ str (String.concat ", " (List.map (fun l -> "~" ^ l) labeled)) ++ str " by label)") ++
          str ", which OCaml checks when the program is built, and Soma never computes")

let () =
  let other = !SomaForeign.describe in
  SomaForeign.describe := (fun c -> match describe c with None -> other c | r -> r);
  let others = !SomaForeign.ocaml_modules in
  SomaForeign.ocaml_modules := (fun () -> ocaml_modules () @ others ())
