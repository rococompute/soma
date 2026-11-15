(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: [Explore model.], for a [Soma.Explore.model]: from each of its
   inputs, each sequence of its actions up to its depth, breadth first, as
   TLC explores a TLA+ specification. States and properties are evaluated
   as [Eval] evaluates a term; one that is a run-time error ([raise] in
   it) is a violation, with the message the evaluation gives
   (GradualErrors.runtime_error). A state already reached from the same
   input is not explored again. *)

open EConstr
open Pp

let explore_ref name = Nametab.global (Libnames.qualid_of_string ("Soma.Explore." ^ name))

let is_ref env sigma name c =
  let f, _ = decompose_app sigma c in
  isRefX env sigma (Rocqlib.lib_ref name) f

(* the elements of a list value *)
let rec elements env sigma c =
  let f, args = decompose_app sigma c in
  if isRefX env sigma (Rocqlib.lib_ref "core.list.cons") f && Array.length args = 3 then
    args.(1) :: elements env sigma args.(2)
  else if isRefX env sigma (Rocqlib.lib_ref "core.list.nil") f then []
  else CErrors.user_err (str "Explore: not a list: " ++ Printer.pr_econstr_env env sigma c ++ str ".")

let rec nat_of env sigma c =
  let f, args = decompose_app sigma c in
  if isRefX env sigma (Rocqlib.lib_ref "num.nat.S") f then 1 + nat_of env sigma args.(0)
  else if isRefX env sigma (Rocqlib.lib_ref "num.nat.O") f then 0
  else CErrors.user_err (str "Explore: the depth is not a number: " ++ Printer.pr_econstr_env env sigma c ++ str ".")

let pair env sigma c =
  let f, args = decompose_app sigma c in
  if isRefX env sigma (Rocqlib.lib_ref "core.prod.intro") f && Array.length args = 4 then args.(2), args.(3)
  else CErrors.user_err (str "Explore: not a pair: " ++ Printer.pr_econstr_env env sigma c ++ str ".")

(* a name, a string: as it is printed, without its quotes *)
let name_of env sigma c =
  let s = Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma c) in
  let n = String.length s in
  if n >= 2 && s.[0] = '"' && s.[n - 1] = '"' then String.sub s 1 (n - 2) else s

let quoted name = str "\"" ++ str name ++ str "\""

type outcome = Value of constr | Error of Pp.t

(* the message, without the "Run-time error: " that it starts with: the
   report says what is one *)
let without_prefix e =
  let s = Pp.string_of_ppcmds e and prefix = "Run-time error: " in
  let n = String.length prefix in
  if String.length s >= n && String.sub s 0 n = prefix then str (String.sub s n (String.length s - n)) else e

let evaluate env sigma t =
  Gradual.clear_failures ();
  Gradual.reset_steps ();
  try
    let v = Reductionops.nf_all env sigma t in
    (* the calls to WebAssembly modules, computed (SomaForeign) *)
    let v = SomaForeign.evaluate ~reduce:(Reductionops.nf_all env sigma) env sigma v in
    if Gradual.enabled env && GradualErrors.mentions_err env sigma v then
      Error (without_prefix (GradualErrors.runtime_error env sigma ~original:t ~failures:(Gradual.failures ())))
    else Value v
  with Gradual.Out_of_steps _ -> Error (str "it does not finish: it was stopped after too many steps.")

(* a step of a behaviour: the action taken (none for the initial state),
   and the state after it *)
type step = { action : constr option; state : constr }

type violation = {
  input : constr;
  behaviour : step list;       (* oldest first; empty: before the initial state *)
  what : Pp.t;
}

let rec explore c =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, m = Constrintern.interp_constr_evars env sigma c in
  let sigma = Typeclasses.resolve_typeclasses env sigma in
  let m = Evarutil.nf_evar sigma m in
  let ty = Reductionops.whd_all env sigma (Retyping.get_type_of env sigma m) in
  let params = match kind sigma ty with
    | App (f, [|i; s; a|]) when isRefX env sigma (explore_ref "model") f -> [|i; s; a|]
    | _ -> CErrors.user_err (str "Explore takes a Soma.Explore.model, not a " ++
                             Printer.pr_econstr_env env sigma ty ++ str ".")
  in
  (* soma explore reviews, and explores, every model: its Explore
     commands do not stop it *)
  if Sys.getenv_opt "SOMA_REVIEW" = Some "1" then ()
  else match explore_model env sigma m params with
  | false, message -> Feedback.msg_notice message
  | true, message -> CErrors.user_err message

(* the model [m], of type [model params]: whether a violation was found,
   and the report (the violations, then what was explored) *)
and explore_model env sigma m params =
  let field name extra =
    let sigma', proj = Evd.fresh_global env sigma (explore_ref name) in
    ignore sigma';
    mkApp (proj, Array.concat [params; [|m|]; extra])
  in
  let value what t = match evaluate env sigma t with
    | Value v -> v
    | Error e -> CErrors.user_err (str "Explore: its " ++ str what ++ str " is a run-time error: " ++ e)
  in
  let inputs = elements env sigma (value "inputs" (field "inputs" [||])) in
  let actions = elements env sigma (value "actions" (field "actions" [||])) in
  let depth = nat_of env sigma (value "depth" (field "depth" [||])) in
  let named what l = List.map (fun p -> let n, f = pair env sigma p in name_of env sigma n, f)
      (elements env sigma (value what l)) in
  let invariants = named "invariants" (field "invariants" [||]) in
  let steps = named "steps" (field "steps" [||]) in
  let pr t = Printer.pr_econstr_env env sigma t in
  let violations = ref [] in
  let states = ref 0 and transitions = ref 0 in
  let distinct = ref [] in
  let note_state s =
    incr states;
    if not (List.exists (fun s' -> EConstr.eq_constr_nounivs sigma s s') !distinct) then distinct := s :: !distinct in
  (* a property, true, false, or a run-time error *)
  let holds input behaviour name t =
    match evaluate env sigma t with
    | Value v when is_ref env sigma "core.bool.true" v -> true
    | Value v when is_ref env sigma "core.bool.false" v ->
      violations := { input; behaviour; what = quoted name ++ str " does not hold" } :: !violations; false
    | Value v ->
      violations := { input; behaviour; what = quoted name ++ str " is not true or false: " ++ pr v } :: !violations; false
    | Error e ->
      violations := { input; behaviour; what = quoted name ++ str " is a run-time error: " ++ e } :: !violations; false
  in
  let check_state input behaviour s =
    List.for_all (fun (name, p) -> holds input behaviour name (mkApp (p, [|s|]))) invariants in
  List.iter (fun input ->
      match evaluate env sigma (field "initial" [|input|]) with
      | Error e -> violations := { input; behaviour = []; what = str "the initial state is a run-time error: " ++ e } :: !violations
      | Value s0 ->
        note_state s0;
        let b0 = [{ action = None; state = s0 }] in
        if check_state input b0 s0 then begin
          (* breadth first; a state reached before, from this input, is not explored again *)
          let seen = ref [s0] in
          let frontier = ref [(s0, b0)] in
          for _ = 1 to depth do
            let next = ref [] in
            List.iter (fun (s, behaviour) ->
                List.iter (fun a ->
                    incr transitions;
                    match evaluate env sigma (field "transition" [|a; s|]) with
                    | Error e ->
                      violations := { input; behaviour = behaviour @ [{ action = Some a; state = s }];
                                      what = str "the action " ++ pr a ++ str " is a run-time error: " ++ e } :: !violations
                    | Value s' ->
                      note_state s';
                      let behaviour' = behaviour @ [{ action = Some a; state = s' }] in
                      let ok_steps = List.for_all (fun (name, p) ->
                          holds input behaviour' name (mkApp (p, [|s; s'|]))) steps in
                      if ok_steps && check_state input behaviour' s'
                         && not (List.exists (fun x -> EConstr.eq_constr_nounivs sigma x s') !seen) then begin
                        seen := s' :: !seen;
                        next := (s', behaviour') :: !next
                      end) actions)
              !frontier;
            frontier := List.rev !next
          done
        end) inputs;
  let violations = List.rev !violations in
  let pr_behaviour = function
    | [] -> mt ()
    | b ->
      fnl () ++ str "  The behaviour up to it:" ++
      prlist (fun (k, st) ->
          fnl () ++ str ("    " ^ string_of_int k ^ ": ") ++
          (match st.action with None -> str "initial" | Some a -> pr a) ++
          str "  " ++ hov 0 (pr st.state))
        (List.mapi (fun k st -> k, st) b)
  in
  let report = prlist_with_sep fnl (fun (k, v) ->
      hov 2 (str "Violation " ++ int (k + 1) ++ str ", from input " ++ pr v.input ++ str ":" ++ spc () ++ v.what) ++
      pr_behaviour v.behaviour)
      (List.mapi (fun k v -> k, v) violations) in
  let failing = List.sort_uniq compare (List.map (fun v -> Pp.string_of_ppcmds (pr v.input)) violations) in
  let passing = List.filter (fun i -> not (List.mem (Pp.string_of_ppcmds (pr i)) failing)) inputs in
  let count n one many = int n ++ str " " ++ str (if n = 1 then one else many) in
  let summary =
    str "Explored " ++ count (List.length inputs) "input" "inputs" ++ str ", " ++
    count (List.length actions) "action" "actions" ++
    str ", up to " ++ int depth ++ str " in a row: " ++
    count !states "state" "states" ++ str " (" ++ int (List.length !distinct) ++ str " distinct), " ++
    count !transitions "action taken" "actions taken" ++ str ", " ++
    count (List.length invariants) "invariant" "invariants" ++ str " and " ++
    count (List.length steps) "step property" "step properties" ++ str " checked."
  in
  let passed = match passing with
    | [] -> mt ()
    | l -> fnl () ++ hov 2 (str "No violation from:" ++ spc () ++ prlist_with_sep pr_comma pr l ++ str ".")
  in
  if violations = [] then false, summary ++ str " No violation."
  else
    true, report ++ fnl () ++ summary ++ fnl () ++
          count (List.length violations) "violation" "violations" ++ str ", from " ++
          int (List.length failing) ++ str " of the " ++ count (List.length inputs) "input" "inputs" ++
          str "." ++ passed

(* Soma: [Review.], which [soma explore FILE] runs at the end of FILE: what
   the program and the files of its project that it imports define,
   reviewed for what static guarantees they give up, and where those do
   not hold.

   - Models: each [Soma.Explore.model] defined is explored.
   - Escape hatches, where static types are given up: a definition whose
     type has [Any], the casts of its body (what it makes an [Any] from,
     and uses one as), and its [?] and [raise].
   - Issues, where a guarantee does not hold: a cast from [Any] that fails
     for some of what the value may be (GradualTyping.casts_that_may_fail);
     a theorem whose statement has one, which is then about [raise] for
     those values; what is assumed (an Axiom, a Parameter, an Admitted
     proof) and what rests on it; a proof whose evidence is a gradual
     primitive.
   - Effects: what [main], in a Sandbox program, does outside the program.

   It fails when a model has a violation or there is an issue. *)

open Names

let rec root_dp = function
  | ModPath.MPfile d -> d
  | ModPath.MPdot (m, _) -> root_dp m
  | ModPath.MPbound _ -> DirPath.empty

let contains ~sub s =
  let n = String.length sub and m = String.length s in
  let rec at i = i + n <= m && (String.sub s i n = sub || at (i + 1)) in
  at 0

(* the library being compiled, and those of the project's .soma-cache it
   loaded (vernac/somaImport.ml) *)
let project_libraries () =
  Lib.library_dp () ::
  List.filter (fun dir -> match Loadpath.locate_absolute_library dir with
      | Ok f -> contains ~sub:"/.soma-cache/" f
      | Error _ -> false) (Library.loaded_libraries ())

(* the schemes and other definitions Rocq makes of a declaration *)
let generated c =
  let s = Id.to_string (Constant.label c) in
  List.exists (fun suffix -> String.ends_with ~suffix s) ["_rect"; "_rec"; "_ind"; "_sind"; "_rect_dep"; "_rec_dep"]
  || contains ~sub:"internal_" s

let project_constants env libs =
  Environ.fold_constants (fun c cb acc ->
      if List.exists (DirPath.equal (root_dp (Constant.modpath c))) libs && not (generated c)
      then (c, cb) :: acc else acc) env []
  |> List.sort (fun (a, _) (b, _) -> Constant.CanOrd.compare a b)

let is_proposition env t =
  try
    let s = Retyping.get_sort_of env Evd.empty (EConstr.of_constr t) in
    Sorts.is_prop (EConstr.ESorts.kind Evd.empty s)
  with e when CErrors.noncritical e -> false

let body_of ~opaque_access cb = match cb.Declarations.const_body with
  | Declarations.Def b -> Some b
  | Declarations.OpaqueDef o ->
    (try Some (fst (Global.force_proof opaque_access o)) with e when CErrors.noncritical e -> None)
  | _ -> None

(* The escape hatches of a body, itself and not what it uses: its casts,
   by types (what it makes an Any from, uses one as, or casts between),
   and its [?] and [raise] at other types than sorts *)
type hatches = {
  makes_any_from : Constr.t list;
  uses_any_as : Constr.t list;
  other_casts : (Constr.t * Constr.t) list;
  unknowns : int;
  raises : int;
}

let hatches_of env body =
  let h = ref { makes_any_from = []; uses_any_as = []; other_casts = []; unknowns = 0; raises = 0 } in
  let is_any t = GradualTyping.is_unknown_type env Evd.empty (EConstr.of_constr t) in
  let closed t = EConstr.Vars.closed0 Evd.empty (EConstr.of_constr t) in
  let add l t = if List.exists (Constr.equal t) l then l else l @ [t] in
  let is_sort t = match Constr.kind t with Constr.Sort _ -> true | _ -> false in
  let rec visit c =
    match Constr.kind c with
    | Constr.App (f, args) ->
      let kind = match Constr.kind f with
        | Constr.Const (k, _) -> Gradual.kind_of env k | _ -> None in
      begin match kind, args with
        | Some Gradual.GCast, [|a; b; v|] ->
          if closed a && closed b then begin
            if is_any b && not (is_any a) then h := { !h with makes_any_from = add !h.makes_any_from a }
            else if is_any a && not (is_any b) then h := { !h with uses_any_as = add !h.uses_any_as b }
            else if not (is_any a) && not (is_any b) then
              if not (List.exists (fun (x, y) -> Constr.equal x a && Constr.equal y b) !h.other_casts)
              then h := { !h with other_casts = !h.other_casts @ [(a, b)] }
          end;
          visit v
        | Some Gradual.GUnknown, [|a|] -> if not (is_sort a) then h := { !h with unknowns = !h.unknowns + 1 }
        | Some Gradual.GErr, [|a|] -> if not (is_sort a) then h := { !h with raises = !h.raises + 1 }
        | _ -> visit f; Array.iter visit args
      end
    | _ -> Constr.iter visit c
  in
  visit body;
  !h

(* What [main] does outside the program: the actions of Sandbox's [io] it
   reaches, through the definitions of the project *)
let effects_of_main ~opaque_access env libs =
  match (try Some (Nametab.global (Libnames.qualid_of_string "Soma.Sandbox.io")) with e when CErrors.noncritical e -> None) with
  | Some (GlobRef.IndRef io) ->
    let main = Constant.make2 (ModPath.MPfile (Lib.library_dp ())) (Id.of_string "main") in
    if not (Environ.mem_constant main env) then None else begin
      let found = ref [] and seen = ref [] in
      let note what = if not (List.mem what !found) then found := !found @ [what] in
      let name j = Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty (GlobRef.ConstructRef (io, j))) in
      let rec visit c =
        match Constr.kind c with
        | Constr.App (f, args) ->
          (match Constr.kind f with
           | Constr.Construct ((ind, j), _) when Ind.CanOrd.equal ind io ->
             let n = name j in
             if n = "serve" && Array.length args >= 1 && EConstr.Vars.closed0 Evd.empty (EConstr.of_constr args.(0)) then
               let port = Reductionops.nf_all env (Evd.from_env env) (EConstr.of_constr args.(0)) in
               note ("serve (port " ^ Pp.string_of_ppcmds (Printer.pr_econstr_env env (Evd.from_env env) port) ^ ")")
             else if not (List.mem n ["ret"; "bind"]) then note n
           | _ -> visit f);
          Array.iter visit args
        | Constr.Construct ((ind, j), _) when Ind.CanOrd.equal ind io ->
          let n = name j in if not (List.mem n ["ret"; "bind"]) then note n
        | Constr.Const (k, _) when List.exists (DirPath.equal (root_dp (Constant.modpath k))) libs
                                && not (List.exists (Constant.CanOrd.equal k) !seen) ->
          seen := k :: !seen;
          (match body_of ~opaque_access (Environ.lookup_constant k env) with Some b -> visit b | None -> ())
        | _ -> Constr.iter visit c
      in
      (match body_of ~opaque_access (Environ.lookup_constant main env) with Some b -> visit b | None -> ());
      Some !found
    end
  | _ -> None

(* The primitives of Soma.Host (theories/Soma/Host.v) that main reaches
   through the project's definitions, in the order it reaches them: what a
   program built for the machine asks of the system it runs on. None when
   main uses none. *)
let host_of_main ~opaque_access env libs =
  let host = DirPath.make (List.rev_map Id.of_string ["Soma"; "Host"]) in
  let main = Constant.make2 (ModPath.MPfile (Lib.library_dp ())) (Id.of_string "main") in
  if not (Environ.mem_constant main env) then None else begin
    let found = ref [] and seen = ref [] in
    let rec visit c =
      match Constr.kind c with
      | Constr.Const (k, _) when DirPath.equal (root_dp (Constant.modpath k)) host ->
        let n = Id.to_string (Constant.label k) in
        if not (List.mem n !found) then found := !found @ [n]
      | Constr.Const (k, _) when List.exists (DirPath.equal (root_dp (Constant.modpath k))) libs
                              && not (List.exists (Constant.CanOrd.equal k) !seen) ->
        seen := k :: !seen;
        (match body_of ~opaque_access (Environ.lookup_constant k env) with Some b -> visit b | None -> ())
      | _ -> Constr.iter visit c
    in
    (match body_of ~opaque_access (Environ.lookup_constant main env) with Some b -> visit b | None -> ());
    if !found = [] then None else Some !found
  end

(* "a string", "an N" *)
let a_or_an env t =
  let p = Printer.pr_constr_env env Evd.empty t in
  let s = Pp.string_of_ppcmds p in
  let n = String.length s in
  let letter_vowel = n > 0 && String.contains "AEFHILMNORSX" s.[0] &&
                     (n = 1 || not (Char.lowercase_ascii s.[1] = s.[1] && Char.uppercase_ascii s.[1] <> s.[1])) in
  let vowel = n > 0 && String.contains "aeiouAEIOU" s.[0] in
  str (if vowel || letter_vowel then "an " else "a ") ++ p

let review ~opaque_access =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let libs = project_libraries () in
  let constants = project_constants env libs in
  (* full names: web.request.start_of *)
  let pr_c c = str (Libnames.string_of_path (Nametab.path_of_global (GlobRef.ConstRef c))) in
  let pr t = Printer.pr_constr_env env Evd.empty t in
  let words s = prlist_with_sep spc str (String.split_on_char ' ' s) in
  let issues = ref [] and violations = ref 0 in
  let issue p =
    let key = Pp.string_of_ppcmds p in
    if not (List.exists (fun q -> Pp.string_of_ppcmds q = key) !issues) then issues := !issues @ [p] in
  let some_types l = prlist_with_sep (fun () -> str " or ") (fun (o : GradualTyping.origin) -> a_or_an env o.otype) l in
  let theorems = List.filter (fun (_, cb) -> is_proposition env cb.Declarations.const_type) constants in
  (* models *)
  let model_ref = try Some (explore_ref "model") with e when CErrors.noncritical e -> None in
  let models = List.filter_map (fun (c, cb) ->
      match model_ref with
      | None -> None
      | Some mref ->
        let ty = Reductionops.whd_all env sigma (EConstr.of_constr cb.Declarations.const_type) in
        match EConstr.kind sigma ty with
        | App (f, [|_; _; _|]) when isRefX env sigma mref f && body_of ~opaque_access cb <> None ->
          let _, args = EConstr.decompose_app sigma ty in
          let failed, message =
            try explore_model env sigma (EConstr.mkConstU (c, EConstr.EInstance.empty)) args
            with e when CErrors.noncritical e -> true, CErrors.print e in
          if failed then incr violations;
          Some (v 2 (pr_c c ++ str ":" ++ fnl () ++ message))
        | _ -> None) constants in
  (* escape hatches, and the issues of the casts of definitions *)
  let hatches = List.filter_map (fun (c, cb) ->
      let typ = cb.Declarations.const_type in
      let theorem = is_proposition env typ in
      let any_in_type = GradualTyping.mentions_unknown env sigma (EConstr.of_constr typ) in
      let body = body_of ~opaque_access cb in
      let h = match body with
        | Some b -> hatches_of env b
        | None -> { makes_any_from = []; uses_any_as = []; other_casts = []; unknowns = 0; raises = 0 } in
      (match body with
       | Some b when not theorem ->
         List.iter (fun (m : GradualTyping.may_fail) ->
             issue (hov 2 (pr_c c ++ str ":" ++ spc () ++ Printer.pr_lconstr_env m.env Evd.empty m.value ++ spc () ++
                           words "is an Any that may be" ++ spc () ++ some_types m.failing ++ str "," ++ spc () ++
                           words "used as" ++ spc () ++ a_or_an env m.target ++ str ":" ++ spc () ++
                           words "a run-time error whenever it is one.")))
           (GradualTyping.casts_that_may_fail env b)
       | _ -> ());
      let types l = Pp.h (prlist_with_sep (fun () -> str ", ") (a_or_an env) l) in
      let lines =
        (match !SomaForeign.describe c with
         | Some d -> [str "is " ++ d]
         | None -> []) @
        (if any_in_type then
           [if theorem then str "its statement has Any" else hov 2 (str "its type has Any:" ++ spc () ++ pr typ)]
         else []) @
        (if h.makes_any_from <> [] then [str "makes an Any from " ++ types h.makes_any_from] else []) @
        (if h.uses_any_as <> [] then [str "uses an Any as " ++ types h.uses_any_as] else []) @
        List.map (fun (a, b) -> str "casts " ++ a_or_an env a ++ str " to " ++ a_or_an env b) h.other_casts @
        (if h.unknowns > 0 then [str "has ? (" ++ int h.unknowns ++ str ")"] else []) @
        (if h.raises > 0 then [str "has raise (" ++ int h.raises ++ str ")"] else [])
      in
      if lines = [] then None
      else Some (v 2 (pr_c c ++ prlist (fun l -> fnl () ++ l) lines))) constants in
  (* issues of theorems, and what is assumed *)
  List.iter (fun (c, cb) ->
      let typ = cb.Declarations.const_type in
      List.iter (fun (m : GradualTyping.may_fail) ->
          issue (hov 2 (pr_c c ++ str ":" ++ spc () ++ words "its statement has" ++ spc () ++
                        Printer.pr_lconstr_env m.env Evd.empty m.value ++ str "," ++ spc () ++
                        words "an Any that may be" ++ spc () ++ some_types m.failing ++ str "," ++ spc () ++
                        words "used as" ++ spc () ++ a_or_an env m.target ++ str ":" ++ spc () ++
                        words "for those values, the theorem is about raise, and says nothing.")))
        (GradualTyping.casts_that_may_fail env typ);
      match body_of ~opaque_access cb with
      | Some body ->
        (match GradualTyping.proof_fake_evidence env ~typ ~body with
         | Some _ -> issue (hov 2 (pr_c c ++ str ":" ++ spc () ++ words "its proof uses a gradual primitive as evidence, so it is not proved."))
         | None -> ())
      | None -> ()) theorems;
  List.iter (fun (c, cb) ->
      match cb.Declarations.const_body with
      | Declarations.Undef _ when Option.is_empty (Gradual.kind_of env c)
                                && Option.is_empty (!SomaForeign.describe c) ->
        issue (hov 2 (pr_c c ++ str ":" ++ spc () ++ words "is assumed (an Axiom, a Parameter or an Admitted proof), not defined or proved."))
      | _ -> ()) constants;
  List.iter (fun (c, _) ->
      let st = Conv_oracle.get_transp_state (Environ.oracle env) in
      let axioms = try
          let _, assums = Assumptions.assumptions opaque_access st [GlobRef.ConstRef c] in
          Printer.ContextObjectMap.fold (fun o _ acc -> match o with
              | Printer.Axiom (Printer.Constant k, _) when Option.is_empty (Gradual.kind_of env k)
                                                       && Option.is_empty (!SomaForeign.describe k)
                                                       && not (Constant.CanOrd.equal k c) -> pr_c k :: acc
              | Printer.Axiom (Printer.Guarded g, _) -> (Printer.pr_global g ++ str " (whose recursion is not checked)") :: acc
              | Printer.Axiom (Printer.TypeInType g, _) -> (Printer.pr_global g ++ str " (Type : Type)") :: acc
              | _ -> acc) assums []
        with e when CErrors.noncritical e -> [] in
      if axioms <> [] then
        issue (hov 2 (pr_c c ++ str ":" ++ spc () ++ words "rests on what is assumed:" ++ spc () ++
                      prlist_with_sep pr_comma (fun x -> x) (List.rev axioms) ++ str ".")))
    theorems;
  let effects = effects_of_main ~opaque_access env libs in
  let host = host_of_main ~opaque_access env libs in
  let section title items empty =
    v 2 (str title ++ (match items with
        | [] -> fnl () ++ str empty
        | l -> prlist (fun i -> fnl () ++ i) l)) in
  let n_issues = List.length !issues in
  let plural n one many = int n ++ str " " ++ str (if n = 1 then one else many) in
  let report =
    str "Review of " ++ DirPath.print (Lib.library_dp ()) ++
    (match List.length libs - 1 with
     | 0 -> mt ()
     | n -> str " and the " ++ plural n "project file" "project files" ++ str " it imports") ++
    str ": " ++ plural (List.length constants - List.length theorems) "definition" "definitions" ++ str ", " ++
    plural (List.length theorems) "theorem" "theorems" ++ str "." ++ fnl () ++ fnl () ++
    section "Models (Soma.Explore), explored:" models "none." ++ fnl () ++ fnl () ++
    section "Escape hatches, where static types are given up:" hatches "none." ++ fnl () ++ fnl () ++
    section "Issues, where a guarantee does not hold:" !issues "none." ++
    (match effects with
     | Some e -> fnl () ++ fnl () ++
                 section "What main does outside the program:" [Pp.h (prlist_with_sep (fun () -> str ", ") str e)] "nothing."
     | None -> mt ()) ++
    (match host with
     | Some h -> fnl () ++ fnl () ++
                 section "What main asks of the machine (Soma.Host's primitives, which Soma carries out and never computes):"
                   [Pp.h (prlist_with_sep (fun () -> str ", ") str h)] "nothing."
     | None -> mt ()) ++ fnl () ++ fnl () ++
    (if n_issues = 0 && !violations = 0 then str "No issue, and no violation."
     else plural !violations "model with a violation" "models with a violation" ++ str ", " ++
          plural n_issues "issue" "issues" ++ str ".")
  in
  (* soma explore fails unless the last line says there is nothing *)
  Feedback.msg_notice report
