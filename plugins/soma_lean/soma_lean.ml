(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: theorems proved in Lean (theories/Soma/Lean.v).

   FILE.definition, next to FILE.lean, declares theorems that FILE.lean
   proves, [name : statement.], about Soma's own definitions: each is a
   parameter (vernac/g_vernac.mlg), which [Lean Bind], at the end of the
   file, checks with Lean before Soma takes it.

   Soma translates to Lean the definitions the statements use, and their
   own, into a module Soma ([def Soma.fib.fib ...]), which FILE.lean
   imports, and each statement, which Lean must find to be the type of
   FILE.lean's theorem of its name ([example : STATEMENT := name]). A
   theorem that depends on [sorryAx] is refused. What is translated is a
   fragment: nat, bool, lists, pairs and options, their functions and
   comparisons, the connectives and quantifiers, [match], and structural
   [Fixpoint]s; anything else is refused, saying what.

   Soma's kernel never sees Lean's proofs: a theorem is an axiom to it,
   whose trust is Lean's kernel, its axioms (which [#print axioms]
   lists), and this translation. [soma explore] lists each as an escape
   hatch, with them. *)

open Names
open Pp

type binding = {
  file : string;                (* FILE.lean, absolute *)
  lean_name : string;
  statement : string;           (* in Lean *)
  axioms : string list;         (* those Lean's proof depends on *)
}

let bindings = Summary.ref ~name:"soma-lean-bindings" Cmap_env.empty

let in_binding : Constant.t * binding -> Libobject.obj =
  Libobject.declare_object @@ Libobject.superglobal_object_nodischarge "Soma Lean binding"
    ~cache:(fun (c, b) -> bindings := Cmap_env.add c b !bindings)
    ~subst:None

exception Not_lean of Pp.t

let not_lean msg = raise (Not_lean msg)

(* * From Soma to Lean *)

let path_of gr = Libnames.string_of_path (Nametab.path_of_global gr)

(* the name a constant is defined under: Stdlib's Nat.add is Corelib's *)
let canonical k = KerName.to_string (Constant.canonical k)

(* How a function of Rocq's libraries is written in Lean, its arguments
   that are types left out *)
type form =
  | Infix of string            (* (a + b) *)
  | Apply of string            (* (List.map f l) *)
  | Prefix of string           (* (¬ a) *)
  | Reorder of string * int list   (* fold_left f l a: List.foldl f a l *)

let functions = [
  "Corelib.Init.Nat.add", Infix "+";
  "Corelib.Init.Nat.mul", Infix "*";
  "Corelib.Init.Nat.sub", Infix "-";
  "Corelib.Init.Nat.div", Infix "/";
  "Corelib.Init.Nat.modulo", Infix "%";
  "Corelib.Init.Nat.pow", Infix "^";
  "Corelib.Init.Nat.max", Apply "max";
  "Corelib.Init.Nat.min", Apply "min";
  "Corelib.Init.Nat.eqb", Apply "Nat.beq";
  "Corelib.Init.Nat.leb", Apply "Nat.ble";
  "Corelib.Init.Nat.ltb", Apply "Nat.blt";
  "Corelib.Init.Datatypes.andb", Infix "&&";
  "Corelib.Init.Datatypes.orb", Infix "||";
  "Corelib.Init.Datatypes.negb", Prefix "!";
  "Corelib.Init.Datatypes.length", Apply "List.length";
  "Corelib.Init.Datatypes.app", Infix "++";
  "Corelib.Init.Datatypes.fst", Apply "Prod.fst";
  "Corelib.Init.Datatypes.snd", Apply "Prod.snd";
  "Corelib.Lists.ListDef.map", Apply "List.map";
  "Corelib.Lists.ListDef.seq", Apply "List.range'";
  "Stdlib.Lists.List.rev", Apply "List.reverse";
  "Stdlib.Lists.List.fold_right", Apply "List.foldr";
  "Stdlib.Lists.List.fold_left", Reorder ("List.foldl", [0; 2; 1]);
  "Corelib.Init.Peano.lt", Infix "<";
  "Corelib.Init.Peano.ge", Infix "≥";
  "Corelib.Init.Peano.gt", Infix ">";
  "Corelib.Init.Logic.not", Prefix "¬";
]

(* inductive types and propositions *)
let inductives = [
  "Corelib.Init.Datatypes.nat", Apply "Nat";
  "Corelib.Init.Datatypes.bool", Apply "Bool";
  "Corelib.Init.Datatypes.list", Apply "List";
  "Corelib.Init.Datatypes.option", Apply "Option";
  "Corelib.Init.Datatypes.prod", Infix "×";
  "Corelib.Init.Logic.True", Apply "True";
  "Corelib.Init.Logic.False", Apply "False";
  "Corelib.Init.Logic.and", Infix "∧";
  "Corelib.Init.Logic.or", Infix "∨";
  "Corelib.Init.Logic.iff", Infix "↔";
  "Corelib.Init.Logic.eq", Infix "=";
  "Corelib.Init.Peano.le", Infix "≤";
]

(* a name that Lean reads as one: letters, digits, _ and ' *)
let lean_ident s =
  let s = String.map (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' as c -> c | _ -> '_') s in
  if s = "" || (match s.[0] with '0'..'9' | '\'' -> true | _ -> false) then "x_" ^ s else s

(* Lean's keywords, which a variable is not named *)
let lean_keywords = ["fun"; "let"; "in"; "match"; "with"; "if"; "then"; "else"; "do"; "by"; "have"; "show";
                     "from"; "at"; "def"; "theorem"; "where"; "open"; "end"; "namespace"; "section"; "λ"]

let fresh used na =
  let base = match na with Name id -> lean_ident (Id.to_string id) | Anonymous -> "x" in
  let base = if List.mem base lean_keywords then base ^ "_" else base in
  let rec go k = let v = if k = 0 then base else base ^ string_of_int k in
    if List.mem v used then go (k + 1) else v in
  go 0

(* A definition of Soma's, in Lean: [def Soma.fib.fib ...]; collected as
   they are met, in the order they are needed *)
type state = {
  mutable defs : (Constant.t * string) list;      (* reversed *)
  mutable pending : Constant.t list;              (* being translated: no recursion between them *)
}

let lean_const_name c =
  "Soma." ^ String.concat "." (List.map lean_ident
                                 (String.split_on_char '.' (path_of (GlobRef.ConstRef c))))

let is_type env sigma c =
  try EConstr.isSort sigma (Reductionops.whd_all env sigma (Retyping.get_type_of env sigma c))
  with e when CErrors.noncritical e -> false

let rec nat_literal env sigma c =
  let f, args = EConstr.decompose_app sigma c in
  match EConstr.kind sigma f with
  | Construct ((ind, j), _) when path_of (GlobRef.IndRef ind) = "Corelib.Init.Datatypes.nat" ->
    if j = 1 && Array.length args = 0 then Some 0
    else if j = 2 && Array.length args = 1 then Option.map succ (nat_literal env sigma args.(0))
    else None
  | _ -> None

let rec term st env sigma (names : string list) c : string =
  let tr = term st env sigma names in
  match nat_literal env sigma c with
  | Some n -> string_of_int n
  | None ->
  match EConstr.kind sigma c with
  | Rel n -> (match List.nth_opt names (n - 1) with Some v -> v | None -> not_lean (str "a variable out of scope"))
  | Sort s -> if EConstr.ESorts.is_prop sigma s then "Prop" else "Type"
  | Cast (c, _, _) -> tr c
  | Prod (na, dom, cod) ->
    let env' = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, dom)) env in
    if EConstr.Vars.noccurn sigma 1 cod && not (is_type env sigma dom && EConstr.isSort sigma (Reductionops.whd_all env sigma dom)) then
      Printf.sprintf "(%s → %s)" (tr dom) (term st env' sigma ("_" :: names) cod)
    else
      let v = fresh names na.Context.binder_name in
      Printf.sprintf "(∀ (%s : %s), %s)" v (tr dom) (term st env' sigma (v :: names) cod)
  | Lambda (na, dom, body) ->
    let env' = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, dom)) env in
    let v = fresh names na.Context.binder_name in
    Printf.sprintf "(fun (%s : %s) => %s)" v (tr dom) (term st env' sigma (v :: names) body)
  | LetIn (na, v, t, body) ->
    let env' = EConstr.push_rel (Context.Rel.Declaration.LocalDef (na, v, t)) env in
    let x = fresh names na.Context.binder_name in
    Printf.sprintf "(let %s : %s := %s; %s)" x (tr t) (tr v) (term st env' sigma (x :: names) body)
  | Case (ci, u, pms, p, iv, scrut, brs) ->
    let (_, _, _, _, brs) = EConstr.expand_case env sigma (ci, u, pms, p, iv, scrut, brs) in
    case st env sigma names ci.Constr.ci_ind scrut brs
  | Fix _ -> not_lean (str "a recursive function inside a term (a fix not at the top of a definition)")
  | _ ->
    let f, args = EConstr.decompose_app sigma c in
    let args = Array.to_list args in
    let shown () = List.map tr (List.filter (fun a -> not (is_type env sigma a)) args) in
    let apply name = match shown () with
      | [] -> name
      | xs -> "(" ^ String.concat " " (name :: xs) ^ ")" in
    let form name = function
      | Infix op -> (match shown () with
          | [a; b] -> Printf.sprintf "(%s %s %s)" a op b
          | xs -> not_lean (str name ++ str " applied to " ++ int (List.length xs) ++ str " arguments, and not 2"))
      | Apply n -> apply n
      | Prefix op -> (match shown () with
          | [a] -> Printf.sprintf "(%s%s)" op a
          | _ -> not_lean (str name ++ str " not applied to one argument"))
      | Reorder (n, order) ->
        let xs = Array.of_list (shown ()) in
        if Array.length xs <> List.length order then not_lean (str name ++ str " not applied to all its arguments")
        else "(" ^ String.concat " " (n :: List.map (fun i -> xs.(i)) order) ^ ")" in
    match EConstr.kind sigma f with
    | Const (k, _) ->
      let name = canonical k in
      (match List.assoc_opt name functions with
       | Some fm -> form name fm
       | None ->
         if GradualTyping.is_unknown_type env sigma c then not_lean (str "Any has no Lean counterpart")
         else apply (definition st k))
    | Ind (ind, _) ->
      let name = path_of (GlobRef.IndRef ind) in
      (match name, args with
       | "Corelib.Init.Logic.eq", [_; a; b] -> Printf.sprintf "(%s = %s)" (tr a) (tr b)
       | "Corelib.Init.Logic.ex", [ty; p] ->
         (match EConstr.kind sigma p with
          | Lambda (na, dom, body) ->
            let env' = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, dom)) env in
            let v = fresh names na.Context.binder_name in
            Printf.sprintf "(∃ (%s : %s), %s)" v (tr ty) (term st env' sigma (v :: names) body)
          | _ -> Printf.sprintf "(∃ x, %s x)" (tr p))
       | _ ->
         match List.assoc_opt name inductives with
         | Some (Infix op) ->
           (match List.map tr args with
            | [a; b] -> Printf.sprintf "(%s %s %s)" a op b
            | _ -> not_lean (str name ++ str " not applied to two arguments"))
         | Some (Apply n) -> (match List.map tr args with [] -> n | xs -> "(" ^ String.concat " " (n :: xs) ^ ")")
         | _ -> not_lean (str "the type " ++ str name ++ str " has no Lean counterpart Soma knows"))
    | Construct ((ind, j), _) ->
      let name = path_of (GlobRef.IndRef ind) in
      let xs = shown () in
      (match name, j, xs with
       | "Corelib.Init.Datatypes.nat", 2, [a] -> Printf.sprintf "(%s + 1)" a
       | "Corelib.Init.Datatypes.bool", 1, [] -> "true"
       | "Corelib.Init.Datatypes.bool", 2, [] -> "false"
       | "Corelib.Init.Datatypes.list", 1, [] -> "[]"
       | "Corelib.Init.Datatypes.list", 2, [h; t] -> Printf.sprintf "(%s :: %s)" h t
       | "Corelib.Init.Datatypes.prod", 1, [a; b] -> Printf.sprintf "(%s, %s)" a b
       | "Corelib.Init.Datatypes.option", 1, [a] -> Printf.sprintf "(some %s)" a
       | "Corelib.Init.Datatypes.option", 2, [] -> "none"
       | "Corelib.Init.Logic.True", 1, [] -> "True.intro"
       | _ -> not_lean (str "the constructor " ++ Printer.pr_global (GlobRef.ConstructRef ((ind, j))) ++
                        str " has no Lean counterpart Soma knows"))
    | _ ->
      (match args with
       | [] -> not_lean (str "the term " ++ Printer.pr_econstr_env env sigma c ++ str " has no Lean counterpart")
       | _ -> "(" ^ String.concat " " (tr f :: List.map tr args) ^ ")")

(* a match: on nat, bool, lists, pairs and options *)
and case st env sigma names ind scrut brs =
  let name = path_of (GlobRef.IndRef ind) in
  let patterns = match name with
    | "Corelib.Init.Datatypes.nat" -> [| (fun _ -> "0"); (function [m] -> m ^ " + 1" | _ -> assert false) |]
    | "Corelib.Init.Datatypes.bool" -> [| (fun _ -> "true"); (fun _ -> "false") |]
    | "Corelib.Init.Datatypes.list" -> [| (fun _ -> "[]"); (function [h; t] -> h ^ " :: " ^ t | _ -> assert false) |]
    | "Corelib.Init.Datatypes.prod" -> [| (function [a; b] -> "(" ^ a ^ ", " ^ b ^ ")" | _ -> assert false) |]
    | "Corelib.Init.Datatypes.option" -> [| (function [a] -> "some " ^ a | _ -> assert false); (fun _ -> "none") |]
    | _ -> not_lean (str "a match on " ++ str name ++ str ", which has no Lean counterpart Soma knows") in
  let arities = (snd (Inductive.lookup_mind_specif env ind)).Declarations.mind_consnrealargs in
  let branch i br =
    let n = arities.(i) in
    let rec take k env names vars c =
      if k = 0 then env, names, List.rev vars, c
      else match EConstr.kind sigma c with
        | Lambda (na, dom, body) ->
          let v = fresh names na.Context.binder_name in
          take (k - 1) (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, dom)) env) (v :: names) (v :: vars) body
        | _ -> not_lean (str "a branch of a match that is not a function of its constructor's arguments") in
    let env', names', vars, body = take n env names [] br in
    let pattern = patterns.(i) vars in
    (* in the branch, a variable matched is its pattern: [fib m] where [m]
       is [k + 1] is [fib (k + 1)], which Lean sees is structural *)
    let names' = match EConstr.kind sigma scrut with
      | Rel j -> List.mapi (fun idx v -> if idx = j - 1 + n then "(" ^ pattern ^ ")" else v) names'
      | _ -> names' in
    Printf.sprintf "\n    | %s => %s" pattern (term st env' sigma names' body) in
  Printf.sprintf "(match %s with%s)" (term st env sigma names scrut)
    (String.concat "" (Array.to_list (Array.mapi branch brs)))

(* [k], a definition of Soma's, in Lean: its name, translated once *)
and definition st k =
  let name = lean_const_name k in
  if List.mem_assoc k st.defs || List.mem k st.pending then name else begin
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let cb = Environ.lookup_constant k env in
    let body = match cb.Declarations.const_body with
      | Declarations.Def b -> EConstr.of_constr b
      | _ -> not_lean (Printer.pr_global (GlobRef.ConstRef k) ++ str " is not a definition of Soma's (it has no body Lean could have)") in
    st.pending <- k :: st.pending;
    let typ = EConstr.of_constr cb.Declarations.const_type in
    (* its parameters, as Lean's *)
    let rec params env names acc t b =
      match EConstr.kind sigma b, EConstr.kind sigma (Reductionops.whd_all env sigma t) with
      | Lambda (na, dom, body), Prod (_, _, cod) ->
        let env' = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, dom)) env in
        let v = fresh names na.Context.binder_name in
        let p = if EConstr.isSort sigma (Reductionops.whd_all env sigma dom)
          then Printf.sprintf "{%s : %s}" v (term st env sigma names dom)
          else Printf.sprintf "(%s : %s)" v (term st env sigma names dom) in
        params env' (v :: names) (p :: acc) cod body
      | _ -> env, names, List.rev acc, t, b in
    let env', names, ps, t, b = params env [] [] typ body in
    let outer = List.rev names in
    let text = match EConstr.kind sigma b with
      | Fix (([|_|], 0), (fnames, ftypes, fbodies)) ->
        (* recursive: the fix is [name] applied to the parameters before it *)
        let self = match outer with [] -> name | vs -> "(" ^ String.concat " " (name :: vs) ^ ")" in
        let env_f = EConstr.push_rec_types (fnames, ftypes, fbodies) env' in
        (* the fix's type is outside it, its body inside *)
        let env'', names'', ps', t', b' =
          params env_f (self :: names) [] (EConstr.Vars.lift 1 ftypes.(0)) fbodies.(0) in
        Printf.sprintf "def %s %s : %s :=\n  %s\n" name (String.concat " " (ps @ ps'))
          (term st env'' sigma names'' t') (term st env'' sigma names'' b')
      | Fix _ -> not_lean (str "a definition of several recursive functions at once")
      | _ ->
        Printf.sprintf "def %s %s : %s :=\n  %s\n" name (String.concat " " ps)
          (term st env' sigma names t) (term st env' sigma names b) in
    st.pending <- List.filter (fun k' -> not (Constant.CanOrd.equal k k')) st.pending;
    st.defs <- (k, text) :: st.defs;
    name
  end

(* * Running Lean *)

let read_file f = In_channel.with_open_bin f In_channel.input_all
let write_file f s = Out_channel.with_open_bin f (fun oc -> output_string oc s)

let rec find_up dir file =
  let f = Filename.concat dir file in
  if Sys.file_exists f then Some f
  else let parent = Filename.dirname dir in if parent = dir then None else find_up parent file

(* [lean ARGS] in [dir], with [dir] in LEAN_PATH: whether it succeeded,
   and what it said *)
let lean ~dir args =
  let out = Filename.concat dir "lean.out" in
  let cmd = Printf.sprintf "cd %s && LEAN_PATH=%s %s > %s 2>&1" (Filename.quote dir) (Filename.quote dir)
      (Filename.quote_command "lean" args) (Filename.quote out) in
  let ok = Sys.command cmd = 0 in
  ok, (try read_file out with Sys_error _ -> "")

let contains s sub =
  let n = String.length sub in
  let rec at i = i + n <= String.length s && (String.sub s i n = sub || at (i + 1)) in
  at 0

let replace_all s ~sub ~by =
  let n = String.length sub in
  let b = Buffer.create (String.length s) in
  let rec go i =
    if i >= String.length s then ()
    else if n > 0 && i + n <= String.length s && String.sub s i n = sub then (Buffer.add_string b by; go (i + n))
    else (Buffer.add_char b s.[i]; go (i + 1)) in
  go 0; Buffer.contents b

let bind file =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let lib = Lib.library_dp () in
  let base = Filename.basename file in
  let modname = Filename.remove_extension base in
  let definition = modname ^ ".definition" in
  if not (SomaOpam.command_exists "lean") then
    CErrors.user_err (str definition ++ str ": Lean checks what " ++ str base ++ str " proves, and lean is not installed:" ++
                      spc () ++ str "see https://lean-lang.org/install (elan).");
  (* the declarations of the file, in Soma's modules, as Lean's namespaces *)
  let rec submodules = function
    | ModPath.MPfile d when DirPath.equal d lib -> Some []
    | ModPath.MPdot (mp, l) -> Option.map (fun p -> p @ [Id.to_string l]) (submodules mp)
    | _ -> None in
  let constants = Environ.fold_constants (fun c cb acc ->
      match submodules (Constant.modpath c) with
      | Some subs -> (c, subs, cb) :: acc
      | None -> acc) env [] in
  let constants = List.sort (fun (a, _, _) (b, _, _) -> Constant.CanOrd.compare a b) constants in
  let st = { defs = []; pending = [] } in
  let theorems = List.map (fun (c, subs, cb) ->
      let name = Id.to_string (Constant.label c) in
      (match cb.Declarations.const_body with
       | Declarations.Undef _ -> ()
       | _ -> CErrors.user_err (str definition ++ str " declares what " ++ str base ++
                                str " proves, and defines nothing: " ++ str name ++ str " is a definition."));
      let typ = EConstr.of_constr cb.Declarations.const_type in
      let is_prop = try EConstr.ESorts.is_prop sigma (Retyping.get_sort_of env sigma typ)
        with e when CErrors.noncritical e -> false in
      if not is_prop then
        CErrors.user_err (hov 0 (str definition ++ str " declares theorems that " ++ str base ++ str " proves:" ++ spc () ++
                                 str name ++ str " : " ++ Printer.pr_econstr_env env sigma typ ++ str " is no statement (a Prop)."));
      let statement = try term st env sigma [] typ
        with Not_lean why ->
          CErrors.user_err (hov 0 (str name ++ str " : " ++ Printer.pr_econstr_env env sigma typ ++
                                   str " is not given to Lean:" ++ spc () ++ why ++ str ".")) in
      c, String.concat "." (subs @ [name]), statement) constants in
  (* the work: the module Soma, FILE.lean, and the check, in the cache *)
  let dir = List.fold_left Filename.concat (SomaOpam.cache_root ())
      ["lean"; modname ^ "-" ^ String.sub (Digest.to_hex (Digest.string file)) 0 8] in
  SomaOpam.mkdir_p dir;
  (match find_up (Filename.dirname file) "lean-toolchain" with
   | Some t -> write_file (Filename.concat dir "lean-toolchain") (read_file t)
   | None -> (try Sys.remove (Filename.concat dir "lean-toolchain") with Sys_error _ -> ()));
  let soma_lean =
    "-- Generated by Soma (plugins/soma_lean): the definitions of Soma's that " ^ definition ^
    "'s statements use, in Lean.\nset_option linter.unusedVariables false\n\n" ^
    String.concat "\n" (List.rev_map snd st.defs) in
  write_file (Filename.concat dir "Soma.lean") soma_lean;
  let fail what out =
    let out = replace_all out ~sub:(Filename.concat dir base) ~by:file in
    let out = replace_all out ~sub:(dir ^ "/") ~by:"" in
    CErrors.user_err (str definition ++ str ": " ++ str what ++ fnl () ++ str (String.trim out)) in
  let ok, out = lean ~dir ["-o"; "Soma.olean"; "Soma.lean"] in
  if not ok then fail ("Lean does not take Soma's definitions, as translated (" ^ dir ^ "/Soma.lean):") out;
  write_file (Filename.concat dir base) (read_file file);
  let ok, out = lean ~dir ["-o"; modname ^ ".olean"; base] in
  if not ok then fail (base ^ " does not compile:") out;
  let check = String.concat "" (List.map (fun (_, lname, statement) ->
      Printf.sprintf "example : %s := @%s\n#print axioms %s\n" statement lname lname) theorems) in
  write_file (Filename.concat dir "Check.lean")
    ("-- Generated by Soma (plugins/soma_lean): each statement of " ^ definition ^
     ", which " ^ base ^ " proves\nimport " ^ modname ^ "\n\n" ^ check);
  let ok, out = lean ~dir ["Check.lean"] in
  if not ok then begin
    (* what Lean says of the statements, and not their axioms *)
    let out = String.concat "\n" (List.filter (fun l -> not (String.starts_with ~prefix:"'" l && contains l "axiom"))
                                     (String.split_on_char '\n' out)) in
    fail (base ^ " does not prove what " ^ definition ^ " declares (" ^ dir ^ "/Check.lean has each statement, in Lean):") out
  end;
  (* the axioms of each proof, as #print axioms says them *)
  let lines = String.split_on_char '\n' out in
  List.iter (fun (c, lname, statement) ->
      let prefix = "'" ^ lname ^ "'" in
      let axioms = List.find_map (fun l ->
          if not (String.starts_with ~prefix l) then None
          else match String.index_opt l '[' , String.index_opt l ']' with
            | Some i, Some j -> Some (List.map String.trim (String.split_on_char ',' (String.sub l (i + 1) (j - i - 1))))
            | _ -> Some []) lines in
      let axioms = Option.default [] axioms in
      if List.mem "sorryAx" axioms then
        CErrors.user_err (str definition ++ str ": " ++ str base ++ str "'s " ++ str lname ++
                          str " is proved with sorry, which proves nothing.");
      Lib.add_leaf (in_binding (c, { file; lean_name = lname; statement; axioms })))
    theorems

let describe c =
  match Cmap_env.find_opt c !bindings with
  | None -> None
  | Some b ->
    Some (str "proved in Lean, by " ++ str (Filename.basename b.file) ++ str "'s " ++ str b.lean_name ++
          str " (" ++ str b.statement ++ str "), which Soma's kernel takes as an axiom" ++
          (if b.axioms = [] then str ", Lean's proof using no axiom"
           else str ", Lean's proof using " ++ str (String.concat ", " b.axioms)))

let () =
  let other = !SomaForeign.describe in
  SomaForeign.describe := (fun c -> match describe c with None -> other c | r -> r)
