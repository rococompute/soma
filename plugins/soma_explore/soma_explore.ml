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

let explore c =
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
  if violations = [] then Feedback.msg_notice (summary ++ str " No violation.")
  else
    CErrors.user_err (report ++ fnl () ++ summary ++ fnl () ++
                      count (List.length violations) "violation" "violations" ++ str ", from " ++
                      int (List.length failing) ++ str " of the " ++ count (List.length inputs) "input" "inputs" ++
                      str "." ++ passed)
