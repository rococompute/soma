(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Context.Rel.Declaration

let { Goptions.get = gradual_typing } =
  Goptions.declare_bool_option_and_ref
    ~key:["Gradual"; "Typing"]
    ~value:false
    ()

let () =
  Goptions.declare_option ~kind:Goptions.IntKind {
    Goptions.optstage = Summary.Stage.Interp;
    optdepr = None;
    optkey = ["Gradual"; "Steps"];
    optread = Gradual.step_limit;
    optwrite = Gradual.set_step_limit;
  }

let () = CErrors.register_handler (function
    | Gradual.Out_of_steps (k, n) ->
      let name = match k with
        | Gradual.GCast -> "cast" | Gradual.GUnknown -> "unknown" | Gradual.GErr -> "err"
      in
      Some Pp.(str "Gradual reduction exceeded " ++ int n ++ str " steps (while reducing " ++
               str name ++ str ")." ++ fnl () ++
               str "Normalization does not hold for gradual terms, so this may be a loop." ++ fnl () ++
               str "Raise the limit with \"Set Gradual Steps <n>.\" or remove it with \"Unset Gradual Steps.\"")
    | _ -> None)

let enabled env =
  gradual_typing ()
  && Option.has_some (Gradual.get env Gradual.GCast)
  && Option.has_some (Gradual.get env Gradual.GUnknown)

let prim env k = match Gradual.get env k with
  | Some c -> mkConstU (c, EInstance.empty)
  | None -> assert false

let is_prim env sigma k t = match kind sigma t with
  | App (f, [|_|]) ->
    begin match kind sigma f with
      | Const (c, _) -> Option.equal (==) (Gradual.kind_of env c) (Some k)
      | _ -> false
    end
  | _ -> false

let is_unknown env sigma t = is_prim env sigma Gradual.GUnknown t

let is_unknown_type env sigma t = is_unknown env sigma (Reductionops.whd_all env sigma t)

(* Consistency is the congruence closure of conversion where [?_A] is related
   to everything. We approximate it structurally on weak head normal forms,
   which is complete for types that are first-order up to conversion.
   Without [?], it is conversion, or cumulativity where Rocq allows it
   ([~cumul], the result and the codomains): sorts are consistent only when
   they are cumulative, so [nat : Prop] and moving a type to a lower
   universe stay static errors. *)
let rec consistent ?(cumul=true) env sigma a b =
  (if cumul then Reductionops.is_conv_leq env sigma a b
   else Reductionops.is_conv env sigma a b) ||
  let a = Reductionops.whd_all env sigma a in
  let b = Reductionops.whd_all env sigma b in
  is_unknown env sigma a || is_unknown env sigma b ||
  match kind sigma a, kind sigma b with
  | Evar _, _ | _, Evar _ -> true
  | Prod (na, a1, b1), Prod (_, a2, b2) ->
    consistent ~cumul:false env sigma a1 a2
    && consistent ~cumul (EConstr.push_rel (LocalAssum (na, a1)) env) sigma b1 b2
  | Lambda (na, a1, b1), Lambda (_, a2, b2) ->
    consistent ~cumul:false env sigma a1 a2
    && consistent ~cumul:false (EConstr.push_rel (LocalAssum (na, a1)) env) sigma b1 b2
  | App (f1, args1), App (f2, args2) ->
    Int.equal (Array.length args1) (Array.length args2)
    && consistent ~cumul:false env sigma f1 f2
    && Array.for_all2 (consistent ~cumul:false env sigma) args1 args2
  | _ -> false

(* Where [consistent] fails: the first pair of subterms, with their
   environment, whose heads are not consistent. *)
let rec inconsistency ?(cumul=true) env sigma a b =
  if consistent ~cumul env sigma a b then None
  else
    let a = Reductionops.whd_all env sigma a in
    let b = Reductionops.whd_all env sigma b in
    let rec first env = function
      | [] -> None
      | (a, b) :: l ->
        if consistent ~cumul:false env sigma a b then first env l
        else inconsistency ~cumul:false env sigma a b
    in
    match kind sigma a, kind sigma b with
    | Prod (na, a1, b1), Prod (_, a2, b2) ->
      if not (consistent ~cumul:false env sigma a1 a2) then
        inconsistency ~cumul:false env sigma a1 a2
      else inconsistency ~cumul (EConstr.push_rel (LocalAssum (na, a1)) env) sigma b1 b2
    | App (f1, args1), App (f2, args2) when Int.equal (Array.length args1) (Array.length args2)
                                         && consistent ~cumul:false env sigma f1 f2 ->
      begin match first env (Array.to_list (Array.map2 (fun a b -> (a, b)) args1 args2)) with
        | Some _ as r -> r
        | None -> Some (env, a, b)
      end
    | _ -> Some (env, a, b)

let cast env sigma ~inferred ~expected v =
  try
    let sigma, c = Typing.checked_appvect env sigma (prim env Gradual.GCast) [|inferred; expected; v|] in
    Some (sigma, c, expected)
  with e when CErrors.noncritical e -> None

(* [consistent], also instantiating evars where the two types agree:
   [vec ?A (S ?n)] against [vec Dyn ?] sets [?A := Dyn], although the whole
   types do not unify ([S ?n] against [?]). Elaboration then checks the
   arguments of [vcons] at [Dyn]. *)
let rec unify_consistent ?(cumul=true) env sigma a b =
  let unify = if cumul then Evarconv.unify_leq_delay else Evarconv.unify_delay in
  match unify env sigma a b with
  | sigma -> Some sigma
  | exception Evarconv.UnableToUnify _ ->
    let a = Reductionops.whd_all env sigma a in
    let b = Reductionops.whd_all env sigma b in
    if is_unknown env sigma a || is_unknown env sigma b then Some sigma
    else
      let fold sigma l1 l2 =
        CArray.fold_left2 (fun sigma a b ->
            Option.bind sigma (fun sigma -> unify_consistent ~cumul:false env sigma a b))
          (Some sigma) l1 l2
      in
      match kind sigma a, kind sigma b with
      | Evar _, _ | _, Evar _ -> Some sigma
      | Prod (na, a1, b1), Prod (_, a2, b2) ->
        Option.bind (unify_consistent ~cumul:false env sigma a1 a2) (fun sigma ->
            unify_consistent ~cumul (EConstr.push_rel (LocalAssum (na, a1)) env) sigma b1 b2)
      | App (f1, args1), App (f2, args2) when Int.equal (Array.length args1) (Array.length args2) ->
        fold sigma (Array.append [|f1|] args1) (Array.append [|f2|] args2)
      | _ -> if consistent ~cumul env sigma a b then Some sigma else None

let coerce_to_type env sigma v ~inferred ~expected =
  if not (enabled env) then None
  else match unify_consistent env sigma inferred expected with
    | Some sigma -> cast env sigma ~inferred ~expected v
    | None -> None

(* In GCIC, [f : ?] used as a function is cast to the germ [? -> ?]. As in
   GCIC^G, this germ lives in the same universe as [?] itself. *)
let coerce_to_product env sigma f ~inferred =
  if not (enabled env) then None
  else
    let ty = Reductionops.whd_all env sigma inferred in
    if is_unknown env sigma ty then
      let anon = Context.make_annot Anonymous ERelevance.relevant in
      let expected = mkProd (anon, ty, Vars.lift 1 ty) in
      cast env sigma ~inferred ~expected f
    else None

let coerce_to_sort env sigma t ~inferred =
  if not (enabled env) then None
  else
    let ty = Reductionops.whd_all env sigma inferred in
    if is_unknown env sigma ty then
      let sigma, s = Evd.new_sort_variable Evd.univ_flexible sigma in
      cast env sigma ~inferred ~expected:(mkSort s) t
    else None
