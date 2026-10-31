(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: [The rest follows.], a search for the rest of a proof, which
   reports the proof it finds as sentences of theories/Soma/Proof.v.

   The goal's variables and hypotheses are taken and assumed
   ([Take x : T.], [Assume that P as H.]); then the goal is proved by
   [soma_auto] ([We conclude that P.]), by it after computing
   ([Computing, we conclude that P.]), by a hypothesis, or by a lemma of
   the loaded libraries whose statement could prove it ([By t, we conclude
   that P.]). Each sentence is printed so that it reads back as the
   statement it is about, and so checks when it is written in place of
   [The rest follows.] (soma build --fill). *)

open Ltac_plugin
open Names
open Pp

(* Run an Ltac tactic, given as text: the sentences of Proof.v are
   Ltac *)
let run s = Tacinterp.interp (Procq.parse_string Pltac.tactic s)

(* Statements as text *)

let one_line s =
  let b = Buffer.create (String.length s) in
  let space = ref false in
  String.iter (fun c ->
      if c = '\n' || c = ' ' || c = '\t' then space := true
      else begin
        if !space && Buffer.length b > 0 then Buffer.add_char b ' ';
        space := false; Buffer.add_char b c
      end) s;
  Buffer.contents b

let printed ?flags env sigma t = one_line (string_of_ppcmds (Printer.pr_econstr_env ?flags env sigma t))

let reads_back env sigma s t =
  try
    let c = Procq.parse_string Procq.Constr.lconstr s in
    (* complete by itself, with the universes it makes ([Type] is a new
       one), which may be those of [t] *)
    let t', ustate = Constrintern.interp_constr env sigma c in
    let sigma = Evd.merge_ustate sigma ustate in
    Option.has_some (Reductionops.infer_conv env sigma t' t)
  with e when CErrors.noncritical e -> false

(* [t] as text that reads back as [t]: printed, or printed in the scope of
   its type, which a sentence does not know (a product of reals is read as
   one of numbers without [%R]) *)
let strip_parens s =
  let n = String.length s in
  if n >= 2 && s.[0] = '(' && s.[n - 1] = ')' then
    (* only when the first parenthesis closes at the end *)
    let rec closes_at i depth =
      if i = n then false
      else match s.[i] with
        | '(' -> closes_at (i + 1) (depth + 1)
        | ')' -> if depth = 1 then i = n - 1 else closes_at (i + 1) (depth - 1)
        | _ -> closes_at (i + 1) depth
    in
    if closes_at 0 0 then String.sub s 1 (n - 2) else s
  else s

let statement env sigma t =
  let s = strip_parens (printed env sigma t) in
  let candidates = s :: List.map (fun k -> "(" ^ s ^ ")%" ^ k) ["R"; "Z"; "Q"; "N"; "nat"; "bool"; "str"] in
  match List.find_opt (fun s -> reads_back env sigma s t) candidates with
  | Some s -> s
  | None ->
    (* what printing leaves out ([length []]: a list of what?), shown *)
    let flags = PrintingFlags.current () in
    let flags = { flags with extern = { flags.extern with implicits = true } } in
    let full = strip_parens (printed ~flags env sigma t) in
    if reads_back env sigma full t then full else s

(* Lemmas that could prove the goal: those whose conclusion has the goal's
   head ([eq], [le], [Nat.Even], ...) and mentions what it mentions, and
   equations that can rewrite it. The closer, the earlier. *)

let rec constants acc c =
  let acc = match Constr.kind c with
    | Constr.Const (k, _) -> GlobRef.Set_env.add (GlobRef.ConstRef k) acc
    | Constr.Ind (i, _) -> GlobRef.Set_env.add (GlobRef.IndRef i) acc
    | Constr.Construct (k, _) -> GlobRef.Set_env.add (GlobRef.ConstructRef k) acc
    | _ -> acc
  in
  Constr.fold constants acc c

let head c = match Constr.kind (fst (Constr.decompose_app c)) with
  | Constr.Const (k, _) -> Some (GlobRef.ConstRef k)
  | Constr.Ind (i, _) -> Some (GlobRef.IndRef i)
  | Constr.Construct (k, _) -> Some (GlobRef.ConstructRef k)
  | _ -> None

let max_candidates = 150

let candidates env sigma goal =
  let goal = EConstr.to_constr ~abort_on_undefined_evars:false sigma goal in
  let goal_head = head goal in
  (* what the goal is about: its operations, not its types or its head *)
  let operations c =
    GlobRef.Set_env.filter (fun gr -> match gr with
        | GlobRef.IndRef _ -> false
        | _ -> not (Option.equal GlobRef.UserOrd.equal (Some gr) goal_head))
      (constants GlobRef.Set_env.empty c) in
  let mentioned = operations goal in
  let eq = Rocqlib.lib_ref_opt "core.eq.type" in
  let eq_sides c = match eq, Constr.kind c with
    | Some e, Constr.App (f, [|_; l; r|]) when Option.equal GlobRef.UserOrd.equal (head f) (Some e) -> Some (head l, head r)
    | _ -> None in
  let goal_sides = eq_sides goal in
  let found = ref [] in
  Search.generic_search env sigma (fun gr _kind _env _sigma typ ->
      let _, concl = Term.decompose_prod typ in
      let concl_constants = operations concl in
      let shared = GlobRef.Set_env.cardinal (GlobRef.Set_env.inter concl_constants mentioned) in
      let applies = Option.has_some goal_head && Option.equal GlobRef.UserOrd.equal (head concl) goal_head in
      let rewrites = match eq, head concl with
        | Some e, Some h when GlobRef.UserOrd.equal e h ->
          let lhs = match Constr.kind concl with
            | Constr.App (_, [|_; l; _|]) -> head l
            | _ -> None in
          (match lhs with Some l -> GlobRef.Set_env.mem l mentioned | None -> false)
        | _ -> false
      in
      if (applies && shared >= 1) || rewrites then
        let extra = GlobRef.Set_env.cardinal concl_constants - shared in
        (* hypotheses, not variables: [A -> B], not [forall x, ...] *)
        let premises = List.length (List.filter (fun (_, t) -> not (Constr.isSort t))
            (List.filter (fun (na, _) -> na.Context.binder_name = Anonymous) (fst (Term.decompose_prod typ)))) in
        (* an equation whose left side is the goal's operation rewrites it *)
        let same_side = match goal_sides, eq_sides concl with
          | Some (gl, gr), Some (l, _) ->
            Option.has_some l && (Option.equal GlobRef.UserOrd.equal l gl || Option.equal GlobRef.UserOrd.equal l gr)
          | _ -> false in
        found := ((if same_side then 30 else 0) + shared * 10 - extra - 3 * premises, gr) :: !found);
  let sorted = List.stable_sort (fun (a, _) (b, _) -> compare b a) !found in
  List.filteri (fun i _ -> i < max_candidates) sorted

(* a candidate that fits closely: an equation about the goal's own
   operation *)
let close_fit score = score >= 30

(* The search *)

(* SOMA_REST_TRACE=1 prints what the search tries, on stderr *)
let trace = Option.has_some (Sys.getenv_opt "SOMA_REST_TRACE")

(* The search stops trying after [budget] seconds *)
let budget = 20.
let deadline = ref 0.

let first_of attempts =
  let rec go = function
    | [] -> Proofview.tclZERO (Failure "no proof found")
    | _ when Unix.gettimeofday () > !deadline -> Proofview.tclZERO (Failure "out of time")
    | a :: rest -> Proofview.tclORELSE (Proofview.tclONCE (a ())) (fun _ -> go rest)
  in
  go attempts

(* The definitions the goal uses that are not Rocq's (Corelib, Stdlib,
   Ltac2), to unfold: the words of the program, of Soma's libraries and of
   other projects, which the libraries' lemmas are not about *)
let rocq_library dp = match List.rev (DirPath.repr dp) with
  | root :: _ -> List.mem (Id.to_string root) ["Corelib"; "Stdlib"; "Ltac2"]
  | [] -> false

let unfoldable env k =
  not (rocq_library (ModPath.dp (Constant.modpath k))) &&
  match (Environ.lookup_constant k env).Declarations.const_body with
  | Declarations.Def _ -> true
  | _ -> false

(* The definitions at the top of the goal: its head, or the heads of its
   arguments when its head is Rocq's ([=], [<=]): [state_after] in
   [state_after counter clicks = 0], not [counter] *)
let top_definitions env sigma goal =
  let head_const c = match EConstr.kind sigma (fst (EConstr.decompose_app sigma c)) with
    | Constr.Const (k, _) when unfoldable env k -> Some k
    | _ -> None in
  match head_const goal with
  | Some k -> [k]
  | None ->
    let _, args = EConstr.decompose_app sigma goal in
    List.fold_left (fun acc a -> match head_const a with
        | Some k when not (List.exists (Constant.CanOrd.equal k) acc) -> acc @ [k]
        | _ -> acc) [] (Array.to_list args)

let program_definitions env sigma goal =
  match top_definitions env sigma goal with
  | _ :: _ as ks -> ks
  | [] ->
  let rec collect acc c =
    let acc = match EConstr.kind sigma c with
      | Constr.Const (k, _) ->
        let ours = not (rocq_library (ModPath.dp (Constant.modpath k))) in
        let defined = match (Environ.lookup_constant k env).Declarations.const_body with
          | Declarations.Def _ -> true
          | _ -> false in
        if ours && defined && not (List.exists (Constant.CanOrd.equal k) acc) then k :: acc else acc
      | _ -> acc
    in
    EConstr.fold sigma collect acc c
  in
  List.rev (collect [] goal)

let name_of k = Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty (GlobRef.ConstRef k))

(* Prove the goal here, or unfold its definitions (a definition can use
   another: [rounds] times at most), state it, and prove it then *)
let rec conclude rounds =
  Proofview.Goal.enter_one (fun gl ->
      let env = Proofview.Goal.env gl and sigma = Proofview.Goal.sigma gl in
      let goal = Proofview.Goal.concl gl in
      let p = statement env sigma goal in
      let by t =
        if trace then Printf.eprintf "soma_rest: by %s\n%!" t;
        Proofview.tclTHEN (run ("solve [timeout 1 (Soma.Proof.soma_by_quick " ^ t ^ ")]"))
          (Proofview.tclUNIT ["By " ^ t ^ ", we conclude that " ^ p ^ "."]) in
      let hyps = List.filter_map (fun d ->
          let id = Context.Named.Declaration.get_id d in
          let ty = Context.Named.Declaration.get_type d in
          let is_prop = try EConstr.ESorts.is_prop sigma (Retyping.get_sort_of env sigma ty)
            with e when CErrors.noncritical e -> false in
          if is_prop then Some (Id.to_string id) else None)
          (EConstr.named_context env) in
      let lemma gr =
        Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty gr) in
      let ours, rocq's = List.partition (fun (_, gr) ->
          let mp = match gr with
            | GlobRef.ConstRef k -> Some (Constant.modpath k)
            | GlobRef.IndRef (m, _) | GlobRef.ConstructRef ((m, _), _) -> Some (MutInd.modpath m)
            | GlobRef.VarRef _ -> None in
          match mp with Some mp -> not (rocq_library (ModPath.dp mp)) | None -> true)
          (candidates env sigma goal) in
      let rocq_close, rocq_rest = List.partition (fun (score, _) -> close_fit score) rocq's in
      let unfold () =
        match program_definitions env sigma goal with
        | [] -> Proofview.tclZERO (Failure "nothing to unfold")
        | _ when rounds = 0 -> Proofview.tclZERO (Failure "nothing to unfold")
        | ks ->
          Proofview.tclTHEN (run ("unfold " ^ String.concat ", " (List.map name_of ks)))
            (Proofview.Goal.enter_one (fun gl ->
                 let env = Proofview.Goal.env gl and sigma = Proofview.Goal.sigma gl in
                 let p = statement env sigma (Proofview.Goal.concl gl) in
                 Proofview.tclBIND (conclude (rounds - 1))
                   (fun rest -> Proofview.tclUNIT (("We need to show that " ^ p ^ ".") :: rest))))
      in
      first_of (
        [ (fun () -> Proofview.tclTHEN (run "solve [Soma.Proof.soma_auto]")
              (Proofview.tclUNIT ["We conclude that " ^ p ^ "."]));
          (fun () ->
             Proofview.tclTHEN (run "simpl")
               (Proofview.Goal.enter_one (fun gl ->
                    let env = Proofview.Goal.env gl and sigma = Proofview.Goal.sigma gl in
                    let p = statement env sigma (Proofview.Goal.concl gl) in
                    Proofview.tclTHEN (run "solve [Soma.Proof.soma_auto]")
                      (Proofview.tclUNIT ["Computing, we conclude that " ^ p ^ "."])))) ]
        @ List.map (fun h () -> by h) hyps
        @ List.map (fun (_, gr) () -> by (lemma gr)) (ours @ rocq_close)
        @ [unfold]
        @ List.map (fun (_, gr) () -> by (lemma gr)) rocq_rest))

(* Take and assume what the goal gives, then conclude *)
let rec take_then_conclude acc =
  Proofview.Goal.enter_one (fun gl ->
      let env = Proofview.Goal.env gl and sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let ids = Id.Set.of_list (List.map Context.Named.Declaration.get_id (EConstr.named_context env)) in
      match EConstr.kind sigma (Reductionops.whd_all env sigma concl) with
      | Constr.Prod (na, t, b) ->
        let is_prop = try EConstr.ESorts.is_prop sigma (Retyping.get_sort_of env sigma t)
          with e when CErrors.noncritical e -> false in
        let dependent = not (EConstr.Vars.noccurn sigma 1 b) in
        let base = match na.Context.binder_name with
          | Name id when dependent || not is_prop -> id
          | _ -> Id.of_string "H" in
        let id = Namegen.next_ident_away base ids in
        let s = statement env sigma t in
        let sentence =
          if is_prop && not dependent then "Assume that " ^ s ^ " as " ^ Id.to_string id ^ "."
          else "Take " ^ Id.to_string id ^ " : " ^ s ^ "." in
        Proofview.tclTHEN (run ("intro " ^ Id.to_string id))
          (take_then_conclude (sentence :: acc))
      | _ ->
        Proofview.tclORELSE
          (Proofview.tclBIND (conclude 3) (fun proof -> Proofview.tclUNIT (List.rev_append acc proof)))
          (fun _ ->
             let p = statement env sigma concl in
             let still = List.rev_append acc ["We need to show that " ^ p ^ "."] in
             CErrors.user_err
               (str "The rest does not follow. Still to show:" ++ fnl () ++
                prlist_with_sep fnl (fun s -> str ("    " ^ s)) still)))

(* "We need to show that P." is not said when the next sentence says P *)
let rec without_repeats = function
  | a :: (b :: _ as rest) ->
    let prefix = "We need to show that " in
    let n = String.length prefix in
    if String.length a > n && String.sub a 0 n = prefix then
      let p = String.sub a n (String.length a - n) in
      let ends_with s t = String.length s >= String.length t &&
                          String.sub s (String.length s - String.length t) (String.length t) = t in
      if ends_with b (" that " ^ p) then without_repeats rest else a :: without_repeats rest
    else a :: without_repeats rest
  | l -> l

(* [t] without the deprecation warnings of the lemmas it tries, which the
   proof does not use, set back as they were however [t] ends *)
let quietly t =
  let lift f = Proofview.tclLIFT (Proofview.NonLogical.make f) in
  Proofview.tclBIND (lift (fun () ->
      let flags = CWarnings.get_flags () in
      CWarnings.set_flags (flags ^ ",-deprecated"); flags)) (fun flags ->
      let restore = lift (fun () -> CWarnings.set_flags flags) in
      Proofview.tclORELSE
        (Proofview.tclBIND t (fun x -> Proofview.tclTHEN restore (Proofview.tclUNIT x)))
        (fun (e, info) -> Proofview.tclTHEN restore (Proofview.tclZERO ~info e)))

let tac =
  Proofview.tclTHEN (Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
      deadline := Unix.gettimeofday () +. budget)))
  @@ Proofview.tclBIND (quietly (take_then_conclude [])) (fun sentences ->
      let sentences = without_repeats sentences in
      Feedback.msg_notice
        (str "The rest follows, by:" ++ fnl () ++
         prlist_with_sep fnl (fun s -> str ("    " ^ s)) sentences);
      Proofview.tclUNIT ())
