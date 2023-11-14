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
  key : string;             (* the module: FILE.ml, absolute, or a library's, Async *)
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
                      str "it starts with a letter, followed by letters, digits and _.");
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
   [option], products, [float], functions, types of OCaml modules that a
   .definition declares, and type variables ([forall A, ...]), which
   extraction erases as arguments *)
let rec ocaml_type env sigma vars t =
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
    (* nat as extraction has it, O | S of nat: Soma_nat.nat, which
       toplevel/somaOcaml.ml generates *)
    else if is "num.nat.type" then "Soma_nat.nat"
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

(* [OCaml Bind "FILE.ml"]: FILE.definition declares FILE.ml *)
let bind file =
  let base = Filename.basename file in
  bind_module ~key:file ~ml_file:(Some file) ~top:(module_name file)
    ~definition:(Filename.remove_extension base ^ ".definition")

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
      { SomaForeign.ml_file; top; libraries; items = List.rev items } :: acc)
    !modules []

let describe c =
  match Cmap_env.find_opt c !bindings with
  | None -> None
  | Some b ->
    let whose = match CString.Map.find_opt b.key !modules with
      | Some (Some file, _, _) -> str (Filename.basename file) ++ str "'s "
      | _ -> str "OCaml's " in
    let path = b.top ^ "." ^ b.path in
    Some (match b.item with
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
