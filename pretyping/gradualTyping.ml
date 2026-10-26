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

let cast env sigma ~inferred ~expected v =
  try
    let sigma, c = Typing.checked_appvect env sigma (prim env Gradual.GCast) [|inferred; expected; v|] in
    Some (sigma, c, expected)
  with e when CErrors.noncritical e -> None

let coerce_to_type env sigma v ~inferred ~expected =
  if enabled env && consistent env sigma inferred expected then
    cast env sigma ~inferred ~expected v
  else None

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
