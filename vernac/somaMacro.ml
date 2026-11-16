(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: macros. A macro is a function from the code of its arguments to
   code ([list syntax -> syntax], theories/Soma/Macro.v), defined with
   [Macro] in a .lang file. A use of a macro in scope, [m a b], is
   expanded when it is internalized (interp/constrintern.ml): the code of
   [a] and [b] is quoted into [syntax] values, [m] is applied to them and
   evaluated, and the [syntax] value it returns is read back as code,
   which is internalized in place of [m a b]. *)

open Pp
open Names
open Constrexpr
open EConstr

let lang_suffix = ".lang"

let is_lang_file f = Filename.check_suffix f lang_suffix

let file_of_loc = function
  | Some { Loc.fname = Loc.InFile { file; _ }; _ } -> Some file
  | _ -> None

let constructor name = match Rocqlib.lib_ref name with
  | GlobRef.ConstructRef c -> c
  | _ -> CErrors.anomaly (str name ++ str " is not a constructor.")

let mk name = mkConstructU (constructor name, EInstance.empty)

let is name sigma c = match kind sigma c with
  | Construct (c, _) -> Construct.CanOrd.equal c (constructor name)
  | _ -> false

(* Values of Soma's types *)

let syntax_type () = mkIndU (fst (constructor "soma.macro.var"), EInstance.empty)

let rec nat_value n = if n = 0 then mk "num.nat.O" else mkApp (mk "num.nat.S", [|nat_value (n - 1)|])

let bool_value b = mk (if b then "core.bool.true" else "core.bool.false")

let char_value ch =
  let code = Char.code ch in
  mkApp (mk "core.ascii.ascii", Array.init 8 (fun i -> bool_value (code land (1 lsl i) <> 0)))

let string_value s =
  let rec from i = if i = String.length s then mk "core.string.empty"
    else mkApp (mk "core.string.string", [|char_value s.[i]; from (i + 1)|]) in
  from 0

let list_value ty l =
  List.fold_right (fun x rest -> mkApp (mk "core.list.cons", [|ty; x; rest|]))
    l (mkApp (mk "core.list.nil", [|ty|]))

let pair_type ty =
  mkApp (mkIndU (fst (constructor "core.prod.intro"), EInstance.empty), [|ty; ty|])

(* Quoting: the code a macro is given, as a [syntax] value. Code that has
   no [syntax] constructor is kept in [opaque], and quoted as its index *)

let quote opaque e =
  let syntax = syntax_type () in
  let keep e =
    opaque := !opaque @ [e];
    mkApp (mk "soma.macro.opaque", [|nat_value (List.length !opaque - 1)|]) in
  let rec q e = match e.CAst.v with
    | CRef (qid, None) -> mkApp (mk "soma.macro.var", [|string_value (Libnames.string_of_qualid qid)|])
    | CPrim (Number n) ->
      begin match NumTok.Signed.to_bigint n with
        | Some z when Z.sign z >= 0 && Z.fits_int z -> mkApp (mk "soma.macro.num", [|nat_value (Z.to_int z)|])
        | _ -> keep e
      end
    | CPrim (String s) -> mkApp (mk "soma.macro.str", [|string_value s|])
    | CApp (f, args) when List.for_all (fun (_, ex) -> Option.is_empty ex) args ->
      mkApp (mk "soma.macro.app", [|q f; list_value syntax (List.map (fun (a, _) -> q a) args)|])
    | CLambdaN (binders, body) ->
      let names = List.concat_map (function
          | CLocalAssum (names, _, Default Glob_term.Explicit, { CAst.v = CHole _ }) -> List.map (fun na -> Some na) names
          | _ -> [None]) binders in
      if List.for_all (function Some { CAst.v = Name _ } -> true | _ -> false) names then
        List.fold_right (fun na body -> match na with
            | Some { CAst.v = Name x } -> mkApp (mk "soma.macro.lam", [|string_value (Id.to_string x); body|])
            | _ -> assert false)
          names (q body)
      else keep e
    | CHole _ -> mk "soma.macro.hole"
    | CLetIn ({ CAst.v = Name x }, value, None, body) ->
      mkApp (mk "soma.macro.letin", [|string_value (Id.to_string x); q value; q body|])
    | CCases (Constr.MatchStyle, None, [scrutinee, None, None], branches) ->
      (* a match whose patterns are simple, else Opaque: the patterns are
         checked before the branches are quoted *)
      begin match List.map (fun { CAst.v = (patterns, body) } -> match patterns with
          | [[p]] -> (qpat p, body)
          | _ -> raise Exit) branches with
      | branches ->
        let pair (p, b) = mkApp (mk "core.prod.intro", [|syntax; syntax; p; q b|]) in
        mkApp (mk "soma.macro.match", [|q scrutinee; list_value (pair_type syntax) (List.map pair branches)|])
      | exception Exit -> keep e
      end
    | _ -> keep e
  (* a pattern: a name, a number, a string, [_], or a constructor applied
     to patterns; any other raises Exit *)
  and qpat p = match p.CAst.v with
    | CPatAtom None -> mk "soma.macro.hole"
    | CPatAtom (Some qid) -> mkApp (mk "soma.macro.var", [|string_value (Libnames.string_of_qualid qid)|])
    | CPatPrim (Number n) ->
      begin match NumTok.Signed.to_bigint n with
        | Some z when Z.sign z >= 0 && Z.fits_int z -> mkApp (mk "soma.macro.num", [|nat_value (Z.to_int z)|])
        | _ -> raise Exit
      end
    | CPatPrim (String s) -> mkApp (mk "soma.macro.str", [|string_value s|])
    | CPatCstr (qid, None, args) ->
      let c = mkApp (mk "soma.macro.var", [|string_value (Libnames.string_of_qualid qid)|]) in
      mkApp (mk "soma.macro.app", [|c; list_value syntax (List.map qpat args)|])
    | _ -> raise Exit
  in
  q e

(* Reading back: the code a [syntax] value stands for *)

exception Not_code of EConstr.t

let rec nat_of sigma c =
  if is "num.nat.O" sigma c then 0
  else match kind sigma c with
    | App (f, [|n|]) when is "num.nat.S" sigma f -> 1 + nat_of sigma n
    | _ -> raise (Not_code c)

let string_of sigma c =
  let b = Buffer.create 16 in
  let rec aux c =
    if is "core.string.empty" sigma c then Buffer.contents b
    else match kind sigma c with
      | App (f, [|ch; rest|]) when is "core.string.string" sigma f ->
        begin match kind sigma ch with
          | App (a, bits) when is "core.ascii.ascii" sigma a && Array.length bits = 8 ->
            let code = Array.fold_right (fun bit code ->
                2 * code + (if is "core.bool.true" sigma bit then 1
                            else if is "core.bool.false" sigma bit then 0
                            else raise (Not_code bit))) bits 0 in
            Buffer.add_char b (Char.chr code); aux rest
          | _ -> raise (Not_code ch)
        end
      | _ -> raise (Not_code c)
  in
  aux c

let rec list_of sigma c =
  match kind sigma c with
  | App (f, [|_|]) when is "core.list.nil" sigma f -> []
  | App (f, [|_; x; rest|]) when is "core.list.cons" sigma f -> x :: list_of sigma rest
  | _ -> raise (Not_code c)

let unquote ?loc ~macro sigma opaque c =
  let rec u c =
    if is "soma.macro.hole" sigma c then CAst.make ?loc (CHole None)
    else match kind sigma c with
      | App (f, [|name|]) when is "soma.macro.var" sigma f ->
        CAst.make ?loc (CRef (Libnames.qualid_of_string ?loc (string_of sigma name), None))
      | App (f, [|n|]) when is "soma.macro.num" sigma f ->
        CAst.make ?loc (CPrim (Number (NumTok.Signed.of_int_string (string_of_int (nat_of sigma n)))))
      | App (f, [|s|]) when is "soma.macro.str" sigma f -> CAst.make ?loc (CPrim (String (string_of sigma s)))
      | App (f, [|g; args|]) when is "soma.macro.app" sigma f ->
        begin match list_of sigma args with
          | [] -> u g
          | args -> CAst.make ?loc (CApp (u g, List.map (fun a -> u a, None) args))
        end
      | App (f, [|x; body|]) when is "soma.macro.lam" sigma f ->
        let x = CAst.make ?loc (Name (Id.of_string (string_of sigma x))) in
        CAst.make ?loc (CLambdaN ([CLocalAssum ([x], None, Default Glob_term.Explicit, CAst.make ?loc (CHole None))], u body))
      | App (f, [|x; value; body|]) when is "soma.macro.letin" sigma f ->
        let x = CAst.make ?loc (Name (Id.of_string (string_of sigma x))) in
        CAst.make ?loc (CLetIn (x, u value, None, u body))
      | App (f, [|scrutinee; branches|]) when is "soma.macro.match" sigma f ->
        let branch b = match kind sigma b with
          | App (pr, [|_; _; p; body|]) when is "core.prod.intro" sigma pr ->
            CAst.make ?loc ([[upat p]], u body)
          | _ -> raise (Not_code b) in
        CAst.make ?loc (CCases (Constr.MatchStyle, None, [u scrutinee, None, None],
                                List.map branch (list_of sigma branches)))
      | App (f, [|i|]) when is "soma.macro.opaque" sigma f ->
        begin match List.nth_opt opaque (nat_of sigma i) with
          | Some e -> e
          | None -> CErrors.user_err ?loc (str "The macro " ++ str macro ++ str " returned Opaque "
                                           ++ int (nat_of sigma i) ++ str ", which is not the code of one of its arguments.")
        end
      | App (f, [|message|]) when is "soma.macro.error" sigma f ->
        CErrors.user_err ?loc (str (string_of sigma message))
      | _ -> raise (Not_code c)
  (* a pattern: Var, Num, Str, Hole, or App of a Var to patterns *)
  and upat c =
    let pat p = CAst.make ?loc p in
    let name n = Libnames.qualid_of_string ?loc (string_of sigma n) in
    if is "soma.macro.hole" sigma c then pat (CPatAtom None)
    else match kind sigma c with
      | App (f, [|n|]) when is "soma.macro.var" sigma f -> pat (CPatAtom (Some (name n)))
      | App (f, [|n|]) when is "soma.macro.num" sigma f ->
        pat (CPatPrim (Number (NumTok.Signed.of_int_string (string_of_int (nat_of sigma n)))))
      | App (f, [|s|]) when is "soma.macro.str" sigma f -> pat (CPatPrim (String (string_of sigma s)))
      | App (f, [|g; args|]) when is "soma.macro.app" sigma f ->
        begin match kind sigma g, list_of sigma args with
          | App (v, [|n|]), [] when is "soma.macro.var" sigma v -> pat (CPatAtom (Some (name n)))
          | App (v, [|n|]), args when is "soma.macro.var" sigma v -> pat (CPatCstr (name n, None, List.map upat args))
          | _ -> CErrors.user_err ?loc (str "The macro " ++ str macro ++ str " returned a pattern that applies something other than a name.")
        end
      | _ -> CErrors.user_err ?loc (str "The macro " ++ str macro ++ str " returned a pattern that is not a name, a number, a string, _, or a constructor applied to patterns.")
  in
  u c

(* Expansion *)

let expand env ?loc c args =
  let macro = Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty (GlobRef.ConstRef c)) in
  let sigma = Evd.from_env env in
  let opaque = ref [] in
  let quoted = list_value (syntax_type ()) (List.map (quote opaque) args) in
  let call = mkApp (mkConstU (c, EInstance.empty), [|quoted|]) in
  Gradual.clear_failures ();
  let result = Reductionops.nf_all env sigma call in
  try unquote ?loc ~macro sigma !opaque result
  with Not_code _ ->
    let why =
      if GradualErrors.mentions_err env sigma result then
        GradualErrors.runtime_error env sigma ~original:call ~failures:(Gradual.failures ())
      else str "It returned " ++ Printer.pr_econstr_env env sigma result ++ str "." in
    CErrors.user_err ?loc (hov 0 (str "The macro " ++ str macro ++ str " did not return code."
                                  ++ fnl () ++ why))

let () = SomaMacros.expand := expand

(* The Macro command, in .lang files only *)

let check_in_lang_file ?loc () =
  match file_of_loc loc with
  | Some f when is_lang_file f -> ()
  | _ -> CErrors.user_err ?loc (str "Macro can only be used in a .lang file: macros for FILE.soma go in FILE.lang.")

let global_ref ?loc name =
  CAst.make ?loc (CRef (Libnames.qualid_of_path ?loc (Nametab.path_of_global (Rocqlib.lib_ref name)), None))

let define ?loc ~name ~args body =
  check_in_lang_file ?loc ();
  let syntax = global_ref ?loc "soma.macro.syntax" in
  let list_syntax = CAst.make ?loc (CApp (global_ref ?loc "core.list.type", [syntax, None])) in
  let binder = CLocalAssum ([CAst.make ?loc:args.CAst.loc (Name args.CAst.v)], None, Default Glob_term.Explicit, list_syntax) in
  ComDefinition.do_definition ?loc ~name:name.CAst.v ~poly:PolyFlags.default ~kind:Decls.Definition
    None [binder] None body (Some syntax);
  match Nametab.locate (Libnames.qualid_of_ident name.CAst.v) with
  | GlobRef.ConstRef c -> Lib.add_leaf (SomaMacros.in_macro c)
  | _ -> CErrors.anomaly (str "A macro is not a constant.")

(* A .lang file is loaded in a module of its own, which imports the Macro
   library: the module, and so the file's macros, is then imported where
   the file is loaded, and the Macro library is not. *)

let lang_module file =
  let base = Filename.remove_extension (Filename.basename file) in
  String.map (fun c -> match c with 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> c | _ -> '_') base ^ "_lang"

let lang_prologue file =
  Printf.sprintf "Require Soma.Macro. Module %s. Import Soma.Macro." (lang_module file)

let lang_epilogue file =
  let m = lang_module file in
  Printf.sprintf "End %s. Import %s." m m
