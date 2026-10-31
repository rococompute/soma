(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

open Pp
open Names
open EConstr

let err_constant env = Gradual.get env Gradual.GErr

let is_err env sigma c = match err_constant env, kind sigma c with
  | Some e, App (f, [|_|]) ->
    begin match kind sigma f with
      | Const (c, _) -> Constant.CanOrd.equal c e
      | _ -> false
    end
  | _ -> false

let rec mentions_err env sigma c =
  is_err env sigma c || EConstr.fold sigma (fun b c -> b || mentions_err env sigma c) false c

(* Partial strings: [String c1 (... (String cn rest))], where [rest] is not
   [EmptyString], printed as ["c1...cn" ++ rest] rather than as
   constructors, which the string notation cannot print *)
let partial_strings env sigma c =
  match Rocqlib.lib_ref_opt "core.string.string", Rocqlib.lib_ref_opt "core.string.empty",
        Rocqlib.lib_ref_opt "soma.string.append" with
  | Some (GlobRef.ConstructRef str), Some (GlobRef.ConstructRef empty),
    Some (GlobRef.ConstRef append) ->
    let is_constructor r c = match kind sigma c with
      | Construct (r', _) -> Construct.CanOrd.equal r r'
      | _ -> false
    in
    let rec characters acc c = match kind sigma c with
      | App (f, [|ch; rest|]) when is_constructor str f -> characters (ch :: acc) rest
      | _ -> List.rev acc, c
    in
    let rec aux c = match characters [] c with
      | [], _ -> EConstr.map sigma aux c
      | _, rest when is_constructor empty rest -> c
      | chars, rest ->
        let prefix =
          List.fold_right (fun ch s -> mkApp (mkConstructU (str, EInstance.empty), [|ch; s|])) chars (mkConstructU (empty, EInstance.empty))
        in
        mkApp (mkConstU (append, EInstance.empty), [|prefix; aux rest|])
    in
    aux c
  | _ -> c

(* A failed cast *)

let pr env sigma c = Printer.pr_leconstr_env env sigma c

(* [c], when it prints on one short line *)
let short env sigma c =
  let pp = pr env sigma c in
  let s = string_of_ppcmds pp in
  if String.length s <= 60 && not (String.contains s '\n') then Some pp else None

let normalize env sigma c =
  try Reductionops.nf_all env sigma c with e when CErrors.noncritical e -> c

let is_function env sigma t =
  isProd sigma (try Reductionops.whd_all env sigma t with e when CErrors.noncritical e -> t)

let is_proposition env sigma t =
  try ESorts.is_prop sigma (Retyping.get_sort_of env sigma t)
  with e when CErrors.noncritical e -> false

(* "a nat", "an option nat", "a function of type nat -> nat" *)
let a_value_of env sigma t =
  if is_function env sigma t then str "a function of type " ++ pr env sigma t
  else
    let pp = pr env sigma t in
    let s = string_of_ppcmds pp in
    let n = String.length s in
    (* "an N", "an int": a letter read as a vowel, or a vowel *)
    let vowel = n > 0 && (String.contains "aeiouAEIOU" s.[0] ||
                          (String.contains "AEFHILMNORSX" s.[0] &&
                           (n = 1 || not (Char.lowercase_ascii s.[1] = s.[1] && Char.uppercase_ascii s.[1] <> s.[1])))) in
    str (if vowel then "an " else "a ") ++ pp

let failure_message env sigma { Gradual.expected; actual; value; reason } =
  (* Under a binder, the types and the value may mention variables of the
     term, which cannot be printed *)
  if not (CVars.closed0 expected && CVars.closed0 actual) then str "a cast failed"
  else
    let expected = of_constr expected and actual = of_constr actual in
    match reason with
    | Gradual.FIndices when is_proposition env sigma expected ->
      str "expected a proof of " ++ pr env sigma expected ++
      str ", but got a proof of " ++ pr env sigma actual
    | Gradual.FIndices ->
      str "expected " ++ a_value_of env sigma expected ++
      str ", but got " ++ a_value_of env sigma actual
    | Gradual.FMismatch ->
      let got =
        if is_function env sigma actual then a_value_of env sigma actual
        else if not (CVars.closed0 value) then a_value_of env sigma actual
        else match short env sigma (normalize env sigma (of_constr value)) with
          | Some v -> v ++ str " : " ++ pr env sigma actual
          | None -> a_value_of env sigma actual
      in
      str "expected " ++ a_value_of env sigma expected ++ str ", but got " ++ got

(* An explicit raise *)

(* The constants [c] depends on, through transparent bodies, whose body
   has an [err] of its own: where the program raises. [`Term] when [c]
   itself does. *)
let raise_sites env sigma c =
  match err_constant env with
  | None -> [], false
  | Some e ->
    let visited = ref Cset_env.empty and sites = ref [] in
    let rec scan found t = match Constr.kind t with
      | Constr.Const (cst, _) ->
        if Constant.CanOrd.equal cst e then found := true else visit cst
      | _ -> Constr.iter (scan found) t
    and visit cst =
      if not (Cset_env.mem cst !visited) then begin
        visited := Cset_env.add cst !visited;
        match (Environ.lookup_constant cst env).Declarations.const_body with
        | Declarations.Def b ->
          let found = ref false in
          scan found b;
          if !found then sites := cst :: !sites
        | _ -> ()
      end
    in
    let found = ref false in
    scan found (EConstr.to_constr ~abort_on_undefined_evars:false sigma c);
    List.rev !sites, !found

let location cst = Nametab.cci_src_loc (Globnames.TrueGlobal (GlobRef.ConstRef cst))

(* [file], relative to the current directory when it is in it *)
let relative file =
  let cwd = Sys.getcwd () ^ Filename.dir_sep in
  let n = String.length cwd in
  let file =
    if String.length file > n && String.equal (String.sub file 0 n) cwd then
      String.sub file n (String.length file - n)
    else file
  in
  if String.length file > 2 && String.equal (String.sub file 0 2) "./" then
    String.sub file 2 (String.length file - 2)
  else file

let pr_site cst =
  Printer.pr_constant (Global.env ()) cst ++
  match location cst with
  | Some { Loc.fname = Loc.InFile { file; _ }; line_nb; _ } ->
    str " (" ++ str (relative file) ++ str ":" ++ int line_nb ++ str ")"
  | _ -> mt ()

let raise_message env sigma ~original =
  let sites, in_term = raise_sites env sigma original in
  (* the program's own definitions, which have a location, come first *)
  let sites = match List.filter (fun c -> Option.has_some (location c)) sites with
    | [] -> sites
    | l -> l
  in
  match sites, in_term with
  | [], _ -> str "raise"
  | [cst], false -> str "raise in " ++ pr_site cst
  | l, _ ->
    str "raise in one of " ++ prlist_with_sep pr_comma pr_site l ++
    (if in_term then str ", or in the term" else mt ())

let runtime_error env sigma ~original ~failures =
  let messages = match failures with
    | [] -> [raise_message env sigma ~original]
    | l ->
      (* the same cast may be reduced more than once *)
      let pps = List.map (failure_message env sigma) l in
      List.fold_left (fun acc pp ->
          if List.exists (fun pp' -> string_of_ppcmds pp' = string_of_ppcmds pp) acc then acc
          else acc @ [pp]) [] pps
  in
  prlist_with_sep fnl (fun pp -> hov 2 (str "Run-time error: " ++ pp ++ str ".")) messages
