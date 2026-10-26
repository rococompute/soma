(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Reduction rules of the gradual cast calculus (GCIC^G). See gradual.mli. *)

open Names
open Constr
open Declarations
open Context.Rel.Declaration

type kind = Retroknowledge.gradual_prim = GUnknown | GErr | GCast

let prim_to_string = function
  | GUnknown -> "gradual_unknown"
  | GErr -> "gradual_err"
  | GCast -> "gradual_cast"

let prim_of_string = function
  | "gradual_unknown" -> Some GUnknown
  | "gradual_err" -> Some GErr
  | "gradual_cast" -> Some GCast
  | _ -> None

let arity = function GUnknown | GErr -> 1 | GCast -> 3

let get env k =
  let r = Environ.retroknowledge env in
  match k with
  | GUnknown -> r.Retroknowledge.retro_gradual_unknown
  | GErr -> r.Retroknowledge.retro_gradual_err
  | GCast -> r.Retroknowledge.retro_gradual_cast

let enabled env =
  let r = Environ.retroknowledge env in
  Option.has_some r.Retroknowledge.retro_gradual_unknown
  || Option.has_some r.Retroknowledge.retro_gradual_err
  || Option.has_some r.Retroknowledge.retro_gradual_cast

let kind_of env c =
  let r = Environ.retroknowledge env in
  let is = function
    | None -> false
    | Some c' -> Constant.CanOrd.equal c c'
  in
  if is r.Retroknowledge.retro_gradual_cast then Some GCast
  else if is r.Retroknowledge.retro_gradual_unknown then Some GUnknown
  else if is r.Retroknowledge.retro_gradual_err then Some GErr
  else None

let check_registration env k c =
  let cb = Environ.lookup_constant c env in
  let fail msg =
    CErrors.user_err
      Pp.(str "Cannot register " ++ Constant.print c ++ str " as " ++
          str (prim_to_string k) ++ str ": " ++ str msg ++ str ".")
  in
  let () = match cb.const_body with
    | Undef _ -> ()
    | Def _ | OpaqueDef _ | Primitive _ | Symbol _ -> fail "it must be an axiom"
  in
  let () = match cb.const_universes with
    | Monomorphic -> ()
    | Polymorphic _ -> fail "it must be universe monomorphic"
  in
  let is_type_sort t = match kind t with
    | Sort (Sorts.Type _ | Sorts.Set) -> true
    | _ -> false
  in
  let ok = match k, kind cb.const_type with
    | (GUnknown | GErr), Prod (_, s, a) ->
      is_type_sort s && isRelN 1 a
    | GCast, Prod (_, s1, b) ->
      begin match kind b with
        | Prod (_, s2, c) ->
          begin match kind c with
            | Prod (_, a, b) -> is_type_sort s1 && is_type_sort s2 && isRelN 2 a && isRelN 2 b
            | _ -> false
          end
        | _ -> false
      end
    | _ -> false
  in
  if not ok then
    fail (match k with
        | GUnknown | GErr -> "its type must be [forall A : Type, A]"
        | GCast -> "its type must be [forall A B : Type, A -> B]")

(* Views *)

type head =
  | HProd of Name.t binder_annot * types * types
  | HSort of Sorts.t
  | HInd of pinductive * constr array
  | HUnknown
  | HErr
  | HOther

let view_type env c =
  match kind c with
  | Prod (na, a, b) -> HProd (na, a, b)
  | Sort s -> HSort s
  | Ind pi -> HInd (pi, [||])
  | App (f, args) ->
    begin match kind f with
      | Ind pi -> HInd (pi, args)
      | Const (cst, _) when Int.equal (Array.length args) 1 ->
        begin match kind_of env cst with
          | Some GUnknown -> HUnknown
          | Some GErr -> HErr
          | Some GCast | None -> HOther
        end
      | _ -> HOther
    end
  | _ -> HOther

type tview =
  | TUnknown
  | TErr
  | TCast of constr * constr * constr
  | TConstruct of pconstructor * constr array
  | TOther

let view_term env c =
  match kind c with
  | Construct pc -> TConstruct (pc, [||])
  | App (f, args) ->
    begin match kind f with
      | Construct pc -> TConstruct (pc, args)
      | Const (cst, _) ->
        begin match kind_of env cst, args with
          | Some GUnknown, [|_|] -> TUnknown
          | Some GErr, [|_|] -> TErr
          | Some GCast, [|a; b; t|] -> TCast (a, b, t)
          | _ -> TOther
        end
      | _ -> TOther
    end
  | _ -> TOther

(* Reduction *)

let mk env k args = match get env k with
  | Some c -> Some (mkApp (mkConstU (c, UVars.Instance.empty), args))
  | None -> None

let eta_unknown env k a =
  match k, kind a with
  | (GUnknown | GErr), Prod (na, dom, cod) ->
    Option.map (fun body -> mkLambda (na, dom, body)) (mk env k [|cod|])
  | _ -> None

(* Casting between universes: Prop <= Set <= Type, and Type levels are not
   compared (the reduction machines do not have the universe graph at hand,
   and GCIC^G already gives up normalization). *)
let sort_castable s1 s2 =
  let rank = function
    | Sorts.SProp -> None
    | Sorts.Prop -> Some 0
    | Sorts.Set -> Some 1
    | Sorts.Type _ | Sorts.GSort _ | Sorts.VSort _ -> Some 2
  in
  match s1, s2 with
  | Sorts.SProp, Sorts.SProp -> true
  | _ ->
    match rank s1, rank s2 with
    | Some r1, Some r2 -> r1 <= r2
    | _ -> false

let template_instance mib u = match mib.mind_template with
  | None -> u
  | Some templ -> templ.template_defaults

(* <I pars2 <= I pars1> (c pars1 args) ~> c pars2 (<T2_i <= T1_i> args_i)
   where T1_i / T2_i are the types of the constructor arguments instantiated
   with the source / target parameters and the source / casted arguments. *)
let cast_constructor env cast ((ind, k), _) u1 u2 pars1 pars2 cargs =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let npar = mib.mind_nparams in
  if Array.length cargs <> npar + mip.mind_consnrealargs.(k - 1) then None
  else
    let u1 = template_instance mib u1 and u2 = template_instance mib u2 in
    let ctx, _ = mip.mind_nf_lc.(k - 1) in
    let decls = List.rev ctx in
    let rec go decls i s1 s2 acc = match decls with
      | [] -> List.rev acc
      | LocalAssum (_, ty) :: decls ->
        if i < npar then
          go decls (i + 1) (pars1.(i) :: s1) (pars2.(i) :: s2) acc
        else
          let arg = cargs.(i) in
          let ty1 = Vars.substl s1 (Vars.subst_instance_constr u1 ty) in
          let ty2 = Vars.substl s2 (Vars.subst_instance_constr u2 ty) in
          let arg' =
            if Constr.equal ty1 ty2 then arg
            else mkApp (cast, [|ty1; ty2; arg|])
          in
          go decls (i + 1) (arg :: s1) (arg' :: s2) (arg' :: acc)
      | LocalDef (_, b, _) :: decls ->
        let b1 = Vars.substl s1 (Vars.subst_instance_constr u1 b) in
        let b2 = Vars.substl s2 (Vars.subst_instance_constr u2 b) in
        go decls i (b1 :: s1) (b2 :: s2) acc
    in
    let args = go decls 0 [] [] [] in
    Some (mkApp (mkConstructU ((ind, k), u2), Array.append pars2 (Array.of_list args)))

let reduce_cast env ~whnf a b t t_whnf =
  match get env GCast with
  | None -> None
  | Some cast_cst ->
  let cast = mkConstU (cast_cst, UVars.Instance.empty) in
  let err () = mk env GErr [|b|] in
  let unknown () = mk env GUnknown [|b|] in
  (* Not a rule of GCIC, but admissible: casts between syntactically equal
     types are the identity. This also makes stuck casts on neutral types
     (e.g. type variables) disappear when nothing is to be checked. *)
  if Constr.equal a b then Some t
  else match view_type env a, view_type env b with
  | HErr, _ | _, HErr -> err ()
  | HUnknown, HUnknown -> Some t
  | HUnknown, _ ->
    (* projection out of the unknown type *)
    begin match view_term env (Lazy.force t_whnf) with
      | TCast (a', b', t') when view_type env (whnf b') == HUnknown ->
        Some (mkApp (cast, [|a'; b; t'|]))
      | TUnknown -> unknown ()
      | TErr -> err ()
      | TCast _ | TConstruct _ | TOther -> None
    end
  | _, HUnknown ->
    (* injection into the unknown type: a canonical form, unless the
       injected term is itself unknown or an error *)
    begin match view_term env (Lazy.force t_whnf) with
      | TUnknown -> unknown ()
      | TErr -> err ()
      | TCast _ | TConstruct _ | TOther -> None
    end
  | HProd (_, a1, b1), HProd (na2, a2, b2) ->
    (* <Pi x:A2.B2 <= Pi x:A1.B1> f ~> fun x : A2 => <B2 <= B1[x'/x]> (f x')
       where x' := <A1 <= A2> x *)
    let x' =
      if Constr.equal a1 a2 then mkRel 1
      else mkApp (cast, [|Vars.lift 1 a2; Vars.lift 1 a1; mkRel 1|])
    in
    let b1' = Vars.subst1 x' (Vars.liftn 1 2 b1) in
    let body = mkApp (cast, [|b1'; b2; mkApp (Vars.lift 1 t, [|x'|])|]) in
    Some (mkLambda (na2, a2, body))
  | HSort s1, HSort s2 ->
    if sort_castable s1 s2 then Some t else err ()
  | HInd ((ind1, u1), args1), HInd ((ind2, u2), args2) ->
    if not (Ind.CanOrd.equal ind1 ind2) then err ()
    else
      let mib = Environ.lookup_mind (fst ind1) env in
      let mip = mib.mind_packets.(snd ind1) in
      if mip.mind_nrealargs > 0 then None (* indexed families: unsupported, stuck *)
      else if Array.length args1 <> mib.mind_nparams
           || Array.length args2 <> mib.mind_nparams then None
      else begin match view_term env (Lazy.force t_whnf) with
        | TUnknown -> unknown ()
        | TErr -> err ()
        | TConstruct (pc, cargs) ->
          cast_constructor env cast pc u1 u2 args1 args2 cargs
        | TCast _ | TOther -> None
      end
  | (HProd _ | HSort _ | HInd _), (HProd _ | HSort _ | HInd _) ->
    (* head constructor mismatch *)
    err ()
  | HOther, _ | _, HOther -> None

let inductive_indices env ci a =
  let mib = Environ.lookup_mind (fst ci.ci_ind) env in
  let mip = mib.mind_packets.(snd ci.ci_ind) in
  if mip.mind_nrealargs = 0 then Some [||]
  else if mip.mind_nrealdecls <> mip.mind_nrealargs then None
  else match view_type env a with
    | HInd (_, args) when Array.length args = ci.ci_npar + mip.mind_nrealargs ->
      Some (Array.sub args ci.ci_npar mip.mind_nrealargs)
    | _ -> None
