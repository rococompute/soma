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
  let native = match EConstr.kind sigma t with
    | Const (c, _) -> (match Cmap_env.find_opt c !bindings with
      | Some { item = SomaForeign.OCamlNativeType path; _ } -> Some path
      | Some { item = (SomaForeign.OCamlNativeOwnedRecord r | SomaForeign.OCamlNativeImmutableRecord(r,_)); _ } -> Some(SomaForeign.native_record_type r)
      | Some { item = SomaForeign.OCamlNativeOwnedVariant v; _ } -> Some(SomaForeign.native_variant_type v)
      | Some { item = SomaForeign.OCamlNativeCallableType c; _ } -> Some(SomaForeign.native_callable_type c)
      | _ -> None)
    | Ind((m,0),_) ->
      let symbol=KerName.to_string(MutInd.canonical m)in
      Cmap_env.fold(fun _ binding found->match found,binding.item with
       |None,SomaForeign.OCamlNativeImmutableRecord(r,info)when info.logical_type=symbol->Some(SomaForeign.native_record_type r)
       |_->found)!bindings None
    | _ -> None in
  match native with Some path -> path | None ->
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
    else if is "core.string.type" then "string"
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
    else if is "soma.native.entry" then arg (List.hd args) ^ " Soma_effect.entry"
    else if is "soma.native.callback" then
      "(" ^ String.concat ", " (List.map arg args) ^ ") Soma_effect.callback"
    else if is "soma.native.triple" || is "soma.native.quadruple" then
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
  let constants = List.filter (fun (c, _, _) -> not (Cmap_env.mem c !bindings) && not(generated_logical c)) constants in
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
let native_type ?(external_=false) name path =
  ignore (native_context ());
  if not (Rocqlib.has_ref "soma.native.handle") then native_error "import Soma.Native first";
  let _, _, top = native_context () in
  let path = if external_ then native_path path else top ^ "." ^ native_path path in
  let symbol = native_namespace () ^ "." ^ Id.to_string name in
  let body = native_app (native_global "soma.native.handle") [native_string symbol] in
  let c = native_declare name body None in
  native_register name c (SomaForeign.OCamlNativeType path)

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
let native_variant name cases =
  ignore(native_context());
  if not(Rocqlib.has_ref "soma.native.handle")then native_error "import Soma.Native first";
  if cases=[]then native_error "a polymorphic variant needs at least one tag";
  let tags=List.map(fun(tag,_)->native_variant_tag tag)cases in
  if List.length(List.sort_uniq String.compare tags)<>List.length tags then
    native_error "polymorphic variant tags must be distinct";
  let hashes=List.map native_variant_tag_hash tags in
  if List.length(List.sort_uniq Int.compare hashes)<>List.length hashes then
    native_error "polymorphic variant tag hash collision";
  let env=Global.env()in
  let checked=List.map(fun(tag,syntax)->
    let payload=Option.map(fun syntax->
      let sigma,typ=Constrintern.interp_type_evars env(Evd.from_env env)syntax in
      let rec monomorphic t =
        (match EConstr.kind sigma t with
         | Prod(_,domain,_) when EConstr.isSort sigma domain -> native_error "polymorphic variant payloads must be monomorphic"
         | _->());EConstr.iter sigma monomorphic t in
      monomorphic typ;
      try ocaml_type env sigma [] typ,EConstr.isProd sigma(Reductionops.whd_all env sigma typ) with Not_ocaml why->
        CErrors.user_err(str "OCaml Native variant payload: "++why))syntax in
    syntax,{SomaForeign.case_tag=tag;case_payload=Option.map fst payload;
      case_is_function=(match payload with None->false|Some(_,fn)->fn)})cases in
  let namespace=native_namespace()in
  let handle=native_app(native_global "soma.native.handle")[native_string(namespace^"."^Id.to_string name)]in
  let body=List.fold_right(fun(syntax,_)rest->match syntax with None->rest|Some typ->
    CAst.make(Constrexpr.CLetIn(CAst.make Anonymous,typ,None,rest)))checked handle in
  let c=native_declare name body None in
  let source=match !SomaImport.source_file with Some f->SomaImport.project_file f|None->assert false in
  native_register name c (SomaForeign.OCamlNativeOwnedVariant{
    variant_namespace=namespace;variant_name=Id.to_string name;variant_source=source;variant_cases=List.map snd checked})

let native_callable name syntax =
  ignore(native_context());
  if not(Rocqlib.has_ref "soma.native.handle")then native_error "import Soma.Native first";
  let env=Global.env()in
  let sigma,typ=Constrintern.interp_type_evars env(Evd.from_env env)syntax in
  let rec signature args labels t =
    match EConstr.kind sigma(Reductionops.whd_all env sigma t)with
    | Prod(binder,domain,codomain)->
      if is_sort env sigma domain then native_error "native callable schemas must be monomorphic";
      if not(EConstr.Vars.noccurn sigma 1 codomain)then native_error "native callable result depends on a value";
      let label=match binder.Context.binder_name with
        | Anonymous->None|Name id->Some(ocaml_name ~definition:"native callable"(Id.to_string id))in
      let arg=try ocaml_type env sigma [] domain with Not_ocaml why->CErrors.user_err(str "OCaml Native callable: "++why)in
      signature(arg::args)(label::labels)(EConstr.Vars.subst1(EConstr.mkProp)codomain)
    | _->
      let result=try ocaml_type env sigma [] t with Not_ocaml why->CErrors.user_err(str "OCaml Native callable: "++why)in
      List.rev args,List.rev labels,result in
  let args,labels,result=signature[][]typ in
  if args=[]then native_error "a native callable needs at least one argument";
  let namespace=native_namespace()in
  let handle=native_app(native_global "soma.native.handle")[native_string(namespace^"."^Id.to_string name)]in
  let body=CAst.make(Constrexpr.CLetIn(CAst.make Anonymous,syntax,None,handle))in
  let c=native_declare name body None in
  let source=match !SomaImport.source_file with Some f->SomaImport.project_file f|None->assert false in
  native_register name c(SomaForeign.OCamlNativeCallableType{
    callable_namespace=namespace;callable_name=Id.to_string name;callable_source=source;
    callable_arguments=args;callable_labels=labels;callable_result=result})
let native_callable_type env sigma typ = match EConstr.kind sigma typ with
  | Const(c,_)->(match Cmap_env.find_opt c !bindings with
    | Some{item=SomaForeign.OCamlNativeCallableType c;_}->c
    | _->native_error "Apply needs a declared native callable as its first argument")
  | _->native_error "Apply needs a declared native callable as its first argument"

let native_constructor_path path =
 let parts=String.split_on_char '.' path in
 if parts=[] || List.exists(fun part->not(is_module_name part) || part.[0]<>Char.uppercase_ascii part.[0])parts then
  native_error "a constructor path needs uppercase OCaml module/constructor names";
 path

let native_callback name typ operation =
  ignore (native_context ());
  if not (Rocqlib.has_ref "soma.native.callback") then native_error "import Soma.Native first";
  let env = Global.env () in
  let sigma, typ = Constrintern.interp_type_evars env (Evd.from_env env) typ in
  let fixed_arity = match operation with
    | SomaForeign.NativeGet _ -> Some 1 | SomaForeign.NativeSet _ -> Some 2
    | SomaForeign.NativeBuild fields -> Some(List.length fields)
    | SomaForeign.NativeCopy fields -> Some(1+List.length fields)
    | SomaForeign.NativeCallableApply _ ->
      (match EConstr.kind sigma(Reductionops.whd_all env sigma typ)with
       | Prod(_,domain,_)->Some(1+List.length(native_callable_type env sigma domain).SomaForeign.callable_arguments)
       | _->native_error "Apply needs a native callable argument")
    | SomaForeign.NativeValue _ | SomaForeign.NativeExternalValue _ -> None
    | SomaForeign.NativeVariantView _ | SomaForeign.NativeVariantBuild _
    | SomaForeign.NativeConstructorTag _ | SomaForeign.NativeConstructorCase _ | SomaForeign.NativeExternalConstant _ -> Some 1 in
  let rec arguments previous remaining t =
    if remaining=Some 0 then List.rev previous,t else
    (* Leave native aliases intact: they denote opaque external types. *)
    let known = match EConstr.kind sigma t with Const(c,_) -> Cmap_env.mem c !bindings | _ -> false in
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
  let types = try List.map (ocaml_type env sigma []) args_types,ocaml_type env sigma [] result
    with Not_ocaml why -> CErrors.user_err (str "OCaml Native: " ++ why) in
  let argument_names,result_name = types in
  let field name =
    if String.contains name '.' then native_error "a field is a single name";
    native_path name in
  let record_type t = match EConstr.kind sigma t with
    | Const(c,_) -> (match Cmap_env.find_opt c !bindings with
      | Some {item=(SomaForeign.OCamlNativeType _|SomaForeign.OCamlNativeOwnedRecord _|SomaForeign.OCamlNativeImmutableRecord _);_}->()
      | _->native_error "a record operation needs a declared native type")
    | _->native_error "a record operation needs a declared native type" in
  let variant_type t = match EConstr.kind sigma t with
    | Const(c,_) -> (match Cmap_env.find_opt c !bindings with
      | Some {item=SomaForeign.OCamlNativeOwnedVariant v;_}->v
      | _->native_error "a variant operation needs a declared native polymorphic variant")
    | _->native_error "a variant operation needs a declared native polymorphic variant" in
  (match operation with
   | SomaForeign.NativeExternalConstant _ | SomaForeign.NativeValue _ | SomaForeign.NativeExternalValue _ | SomaForeign.NativeCallableApply _ | SomaForeign.NativeVariantView _ | SomaForeign.NativeVariantBuild _ -> ()
   | SomaForeign.NativeConstructorTag _ | SomaForeign.NativeConstructorCase _ ->
     (let input=List.hd args_types in
      if EConstr.isRefX env sigma (Rocqlib.lib_ref "soma.exception_value.type") input then () else
      match EConstr.kind sigma input with
      |Const(c,_)->(match Cmap_env.find_opt c !bindings with
        |Some{item=SomaForeign.OCamlNativeType _;_}->()
        |_->native_error "constructor operations need a declared native type")
      |_->native_error "constructor operations need a declared native type")
   | SomaForeign.NativeBuild _ -> record_type result
   | SomaForeign.NativeCopy _ -> record_type(List.hd args_types);record_type result
   | SomaForeign.NativeGet _ | SomaForeign.NativeSet _ -> record_type(List.hd args_types));
  let operation = match operation with
    | SomaForeign.NativeCallableApply _ ->
      let c=native_callable_type env sigma(List.hd args_types)in
      if List.tl argument_names<>c.SomaForeign.callable_arguments || result_name<>c.callable_result then
        native_error "Apply signature differs from the declared callable";
      SomaForeign.NativeCallableApply(Some c)
    | SomaForeign.NativeValue path -> SomaForeign.NativeValue (native_path path)
    | SomaForeign.NativeExternalValue path -> SomaForeign.NativeExternalValue (native_path path)
    | SomaForeign.NativeExternalConstant path ->
      if argument_names<>["unit"]then native_error "an external value getter takes unit";
      SomaForeign.NativeExternalConstant(native_path path)
    | SomaForeign.NativeVariantView _ ->
      if List.length args<>1 then native_error "View needs one native variant argument";
      let v=variant_type(List.hd args_types)in
      if result_name<>SomaForeign.native_variant_view_type v then
        native_error "View result must be the ordered nested result of its payloads (unit for nullary tags)";
      SomaForeign.NativeVariantView(Some v)
    | SomaForeign.NativeVariantBuild(tag,_) ->
      if List.length args<>1 then native_error "Construct needs one payload argument (unit for a nullary tag)";
      let v=variant_type result in
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
    | SomaForeign.NativeGet f ->
      if List.length args<>1 then native_error "Get needs one record argument";
      SomaForeign.NativeGet(field f)
    | SomaForeign.NativeSet f ->
      if List.length args<>2 || result_name<>"unit" then native_error "Set needs record -> value -> unit";
      SomaForeign.NativeSet(field f)
    | SomaForeign.NativeBuild fields | SomaForeign.NativeCopy fields as op ->
      let expected = List.length fields + (match op with SomaForeign.NativeCopy _ -> 1 | _ -> 0) in
      if List.length args<>expected then native_error "record field and argument counts differ";
      if List.length(List.sort_uniq String.compare fields)<>List.length fields then native_error "record fields must be distinct";
      List.iter(fun f->ignore(field f))fields;op in
  (match operation with SomaForeign.NativeValue _ | SomaForeign.NativeExternalValue _ -> () | _ ->
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
  let c = native_declare name body (Some descriptor_type) in
  native_register name c (SomaForeign.OCamlNativeCallback {
    namespace;name=Id.to_string name;arguments=argument_names;result=result_name;labels;operation})

let native_external_constant name result path =
 let typ=CAst.make(Constrexpr.CProdN([Constrexpr.CLocalAssum([CAst.make Anonymous],None,
   Constrexpr.Default Glob_term.Explicit,native_global "core.unit.type")],result))in
 native_callback name typ (SomaForeign.NativeExternalConstant path)

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
        | SomaForeign.OCamlNativeImmutableRecord _ | SomaForeign.OCamlNativeType _ | SomaForeign.OCamlNativeOwnedRecord _ | SomaForeign.OCamlNativeOwnedVariant _ | SomaForeign.OCamlNativeCallableType _ | SomaForeign.OCamlNativeCallback _ ->
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
        | SomaForeign.OCamlNativeCallableType c ->
          str "native callable " ++ str(SomaForeign.native_callable_type c) ++ str ", opaque to Soma"
        | SomaForeign.OCamlNativeOwnedVariant v ->
          str "closed native polymorphic variant " ++ str(SomaForeign.native_variant_type v) ++ str ", opaque to Soma"
        | SomaForeign.OCamlNativeImmutableRecord(r,_) ->
          str "immutable native record " ++ str(SomaForeign.native_record_type r) ++ str ", with a structural logical model"
        | SomaForeign.OCamlNativeOwnedRecord r ->
          str "owned native record " ++ str(SomaForeign.native_record_type r) ++ str ", opaque to Soma"
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
