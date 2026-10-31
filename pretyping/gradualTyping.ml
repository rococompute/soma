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

let mentions_unknown env sigma t =
  let rec aux c = is_unknown env sigma c || EConstr.fold sigma (fun b c -> b || aux c) false c in
  aux (Evarutil.nf_evar sigma t)

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
   [vec ?A (S ?n)] against [vec Any ?] sets [?A := Any], although the whole
   types do not unify ([S ?n] against [?]). Elaboration then checks the
   arguments of [vcons] at [Any]. *)
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

(* The universe of gradual types: casts are between types of
   [Type@{gradual}] (see theories/Corelib/Gradual/Gradual.v). *)
let gradual_sort env =
  let c = Option.get (Gradual.get env Gradual.GCast) in
  match Constr.kind (Environ.lookup_constant c env).Declarations.const_type with
  | Constr.Prod (_, s, _) ->
    begin match Constr.kind s with
      | Constr.Sort s -> Some (ESorts.make s)
      | _ -> None
    end
  | _ -> None

exception Above_gradual of Environ.env * Evd.evar_map * types * types * types

(* When a cast between consistent types cannot be built, say so if a type
   lies above the universe of gradual types. *)
let check_below_gradual env sigma ~inferred ~expected =
  match gradual_sort env with
  | None -> ()
  | Some g ->
    let above ty =
      let s = Retyping.get_sort_of env sigma ty in
      not (Evd.check_leq sigma s g) &&
      match Evd.set_leq_sort sigma s g with
      | _ -> false
      | exception e when CErrors.noncritical e -> true
    in
    let culprit = if above inferred then Some inferred else if above expected then Some expected else None in
    match culprit with
    | None -> ()
    | Some ty -> raise (Above_gradual (env, sigma, inferred, expected, ty))

(* A cast between [?] and an inductive type whose arguments are still
   undetermined evars: nothing will determine them, so they are [?]. At
   type [?], [cons 1 (cons true nil) : Any] would otherwise choose [nat]
   from the first element and reject [true]; from type [?], [snd p] with
   [p : Any] would leave the type of the first component undetermined, and
   [match v with vnil => ... end] with [v : Any] the length of the vector.
   Type parameters become [Any] and indices [?_A]; explicit ones are
   already instantiated. *)
(* Indices are defaulted too, except in a [match] with a return clause
   (see [Cases.compile_cases]): its type may depend on the index, and a
   value whose real index is known would be used at the type computed for
   [?] ([vhead] on a [v : Any], whose result type is
   [match ?_nat with 0 => unit | S _ => A end], that is [?], not [A]). *)
let index_defaulting = ref true

let with_index_defaulting b f =
  let saved = !index_defaulting in
  index_defaulting := b;
  Fun.protect ~finally:(fun () -> index_defaulting := saved) f

(* Inside a [match] whose scrutinee was cast from [?] (see
   [Cases.compile_cases]), the index a branch is at is only known at run
   time: a branch of type [vec B 0] where [vec B n] is expected goes through
   [?], and the cast back checks the index. *)
let gradual_scrutinee = ref false

let with_gradual_scrutinee f =
  let saved = !gradual_scrutinee in
  gradual_scrutinee := false;
  Fun.protect ~finally:(fun () -> gradual_scrutinee := saved) f

let is_gradual_scrutinee () = !gradual_scrutinee

let set_gradual_scrutinee env sigma scrutinees =
  let from_unknown c = match kind sigma c with
    | App (f, [|a; _; _|]) when isConst sigma f ->
      Option.equal (==) (Gradual.kind_of env (fst (destConst sigma f))) (Some Gradual.GCast)
      && is_unknown_type env sigma a
    | _ -> false
  in
  let of_unknown c =
    try is_unknown_type env sigma (Retyping.get_type_of env sigma c)
    with e when CErrors.noncritical e -> false
  in
  if enabled env && List.exists (fun c -> from_unknown c || of_unknown c) scrutinees then
    gradual_scrutinee := true

let default_args_to_unknown env sigma t =
  let t = Reductionops.whd_all env sigma t in
  match kind sigma t with
  | App (f, args) when isInd sigma f ->
    let npar = match kind sigma f with
      | Ind ((mind, _), _) -> (Environ.lookup_mind mind env).Declarations.mind_nparams
      | _ -> 0
    in
    let default sigma a =
      let ty = Reductionops.whd_all env sigma (Retyping.get_type_of env sigma a) in
      try
        let s, d = Typing.checked_appvect env sigma (prim env Gradual.GUnknown) [|ty|] in
        Evarconv.unify_delay env s a d
      with e when CErrors.noncritical e -> sigma
    in
    (* the evars of an argument, also under constructors: the index of
       [cast Any (vec nat (S ?n)) v] is [S ?] (not under binders) *)
    let rec walk sigma a = match kind sigma a with
      | Evar _ -> default sigma a
      | App (f, args) when isConstruct sigma f -> Array.fold_left walk sigma args
      | _ -> sigma
    in
    CArray.fold_left_i (fun i sigma a ->
        if i < npar || !index_defaulting then walk sigma a else sigma)
      sigma args
  | _ -> sigma

let unknown_at env sigma ty =
  if not (enabled env) then None
  else
    try Some (Typing.checked_appvect env sigma (prim env Gradual.GUnknown) [|ty|])
    with e when CErrors.noncritical e -> None

(* The term itself mentions [cast], [unknown] or [err] (not through the
   constants it uses). *)
let mentions_primitive env sigma c =
  let rec aux c = match kind sigma c with
    | Const (cst, _) -> Option.has_some (Gradual.kind_of env cst)
    | _ -> EConstr.fold sigma (fun b c -> b || aux c) false c
  in
  aux c

(* An implicit argument, of a function or of the inductive type of a match
   scrutinee, that nothing determined, in a term that already uses the
   gradual primitives, is [?] when it does not occur in the type of the
   term. [Definition x := nil] mentions no primitive, and its [A] occurs in
   [list A]: it stays unsolved. *)
let default_leftover_implicits env sigma ~typ body =
  if not (enabled env) || not (mentions_primitive env sigma body) then sigma
  else
    let typ = match typ with
      | Some t -> t
      | None -> Retyping.get_type_of env sigma body
    in
    let defaultable sigma evk =
      match snd (Evd.evar_source (Evd.find_undefined sigma evk)) with
      | Evar_kinds.ImplicitArg _ | Evar_kinds.TomatchTypeParameter _ -> true
      | _ -> false
    in
    let default evk sigma =
      if Evd.is_defined sigma evk then sigma
      else
        let evi = Evd.find_undefined sigma evk in
        match unknown_at (Evd.evar_filtered_env env evi) sigma (Evd.evar_concl evi) with
        | Some (sigma, u) -> Evd.define evk u sigma
        | None -> sigma
    in
    let rec loop sigma =
      let in_type = Evarutil.undefined_evars_of_term sigma typ in
      let leftover = Evar.Set.filter
          (fun evk -> defaultable sigma evk && not (Evar.Set.mem evk in_type))
          (Evarutil.undefined_evars_of_term sigma body)
      in
      let sigma' = Evar.Set.fold default leftover sigma in
      if sigma' == sigma then sigma else loop sigma'
    in
    loop sigma

(* [inferred] and [expected] are the same inductive family, with consistent
   parameters (indices may differ). *)
let same_family env sigma inferred expected =
  let a = Reductionops.whd_all env sigma inferred in
  let b = Reductionops.whd_all env sigma expected in
  match kind sigma a, kind sigma b with
  | App (f1, args1), App (f2, args2) when isInd sigma f1 && isInd sigma f2 ->
    let (ind1, _), (ind2, _) = destInd sigma f1, destInd sigma f2 in
    if not (Ind.CanOrd.equal ind1 ind2 && Int.equal (Array.length args1) (Array.length args2))
    then None
    else
      let npar = (Environ.lookup_mind (fst ind1) env).Declarations.mind_nparams in
      let rec params sigma i =
        if i >= npar then Some sigma
        else Option.bind (unify_consistent ~cumul:false env sigma args1.(i) args2.(i))
            (fun sigma -> params sigma (i + 1))
      in
      params sigma 0
  | _ -> None

let coerce_to_type env sigma v ~inferred ~expected =
  if not (enabled env) then None
  else
    let sigma =
      if is_unknown_type env sigma expected then default_args_to_unknown env sigma inferred
      else if is_unknown_type env sigma inferred then default_args_to_unknown env sigma expected
      else sigma
    in
    match unify_consistent env sigma inferred expected with
    | Some sigma ->
      begin match cast env sigma ~inferred ~expected v with
        | Some _ as r -> r
        | None -> check_below_gradual env sigma ~inferred ~expected; None
      end
    | None when !gradual_scrutinee ->
      (* a branch of a match on a value cast from [?], at another index *)
      begin match same_family env sigma inferred expected with
        | None -> None
        | Some sigma ->
          (* its indices that nothing determines, as for a cast from [?] *)
          let sigma = with_index_defaulting true (fun () -> default_args_to_unknown env sigma inferred) in
          Option.bind (unknown_at env sigma (Retyping.get_type_of env sigma expected)) (fun (sigma, dyn) ->
          Option.bind (cast env sigma ~inferred ~expected:dyn v) (fun (sigma, v, _) ->
              cast env sigma ~inferred:dyn ~expected v))
      end
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

(* The gradual primitives a term depends on, through the types and the
   transparent bodies of the constants it mentions (opaque proofs are not
   followed: each proof is checked when it is saved). The cache is part of
   the state, so that backtracking, which may give a name to a different
   constant, also forgets what was computed for it. *)
let uses_cache = Summary.ref ~name:"gradual-uses-cache" Names.Cmap_env.empty

let rec uses env acc c = match Constr.kind c with
  | Constr.Const (cst, _) ->
    begin match Gradual.kind_of env cst with
      | Some k -> if List.mem k acc then acc else k :: acc
      | None -> List.fold_left (fun acc k -> if List.mem k acc then acc else k :: acc) acc (const_uses env cst)
    end
  | _ -> Constr.fold (uses env) acc c

and const_uses env cst =
  match Names.Cmap_env.find_opt cst !uses_cache with
  | Some l -> l
  | None ->
    let cb = Environ.lookup_constant cst env in
    let l = uses env [] cb.Declarations.const_type in
    let l = match cb.Declarations.const_body with
      | Declarations.Def b -> uses env l b
      | _ -> l
    in
    uses_cache := Names.Cmap_env.add cst l !uses_cache;
    l

(* Fake evidence: a gradual primitive whose result is a proof, [unknown P],
   [err P] or [cast A P v] for a proposition [P]. It inhabits any statement,
   so a proof built with it proves nothing. The same primitives at other
   types ([cast nat Any n], [Any] itself) are the gradual program a theorem
   is about, and are not evidence. *)
type fake = { kind : Gradual.kind; env : Environ.env; prop : Constr.t; within : Names.Constant.t option }

let is_proposition env t =
  try
    let s = Retyping.get_sort_of env Evd.empty (EConstr.of_constr t) in
    let s = EConstr.ESorts.kind Evd.empty s in
    Sorts.is_prop s || Sorts.is_sprop s
  with e when CErrors.noncritical e -> false

(* The proposition a gradual primitive applied to [args] stands for, when it
   is one *)
let evidence_for env kind args =
  let target = match kind, args with
    | (Gradual.GUnknown | Gradual.GErr), a :: _ -> Some a
    | Gradual.GCast, _ :: b :: _ :: _ -> Some b
    | _ -> None
  in
  match target with
  | Some p when is_proposition env p ->
    (* as it reads: [Nat.even 3 = true], not [(fun n => Nat.even n = true) 3] *)
    Some (EConstr.Unsafe.to_constr (Reductionops.nf_beta env Evd.empty (EConstr.of_constr p)))
  | _ -> None

let fake_cache = Summary.ref ~name:"gradual-fake-cache" Names.Cmap_env.empty

(* The first fake evidence in [c], under [env]: in [c] itself, and in the
   transparent bodies of the constants it mentions that use gradual
   primitives at all. [allowed] is what may be talked about: a fake that
   occurs in it is the subject of a theorem, not its evidence. *)
let rec find_fake env ~allowed c =
  let allowed_here c = match allowed with
    | Some typ -> Termops.dependent Evd.empty (EConstr.of_constr c) (EConstr.of_constr typ)
    | None -> false
  in
  let found = ref None in
  let rec visit env c =
    if Option.is_empty !found then
      match Constr.kind c with
      | Constr.App (f, args) when (match Constr.kind f with
          | Constr.Const (k, _) -> Option.has_some (Gradual.kind_of env k) | _ -> false) ->
        let k = match Constr.kind f with Constr.Const (k, _) -> k | _ -> assert false in
        let kind = Option.get (Gradual.kind_of env k) in
        (match evidence_for env kind (Array.to_list args) with
         | Some prop when not (allowed_here c) ->
           found := Some { kind; env; prop; within = None }
         | _ -> Array.iter (visit env) args)
      | Constr.Const (cst, _) when Option.is_empty (Gradual.kind_of env cst) ->
        if const_uses env cst <> [] && not (allowed_here c) then
          (match const_fake env cst with
           | Some fk -> found := Some { fk with within = Some (Option.default cst fk.within) }
           | None -> ())
      | _ ->
        Termops.fold_constr_with_full_binders env Evd.empty
          (fun d env -> EConstr.push_rel d env)
          (fun env () c -> visit env (EConstr.Unsafe.to_constr c))
          env () (EConstr.of_constr c)
  in
  visit env c;
  !found

and const_fake env cst =
  match Names.Cmap_env.find_opt cst !fake_cache with
  | Some r -> r
  | None ->
    let cb = Environ.lookup_constant cst env in
    let r = match cb.Declarations.const_body with
      | Declarations.Def b -> find_fake env ~allowed:None b
      | _ -> None
    in
    fake_cache := Names.Cmap_env.add cst r !fake_cache;
    r

let proof_fake_evidence env ~typ ~body =
  if not (Gradual.enabled env) then None
  (* most proofs reach no gradual primitive at all (cached per constant) *)
  else if uses env [] body = [] then None
  else find_fake env ~allowed:(Some typ) body

(* Soma: what a value of type [Any] may be. An [Any] is made from a value
   of a static type by a cast to it ([cast string Any v]); following the
   value back, through the branches of [match]es and into the definitions
   it calls, gives the static types it may have been made from, and where
   ([Among]). A value whose origin is not known, an argument, [?], what a
   recursive function computes, may be anything ([Anything]). A cast from
   [Any] to [T] then fails for each of them that is not consistent with
   [T]: [Any] that may be a [string], used as an [N], is [raise] whenever
   it is a [string]. *)
type origin = { otype : Constr.types; made_in : Names.Constant.t option }
type possible = Anything | Among of origin list

let union a b = match a, b with
  | Anything, _ | _, Anything -> Anything
  | Among l1, Among l2 ->
    Among (l1 @ List.filter (fun o -> not (List.exists (fun o' -> Constr.equal o.otype o'.otype) l1)) l2)

let gradual_kind env f = match Constr.kind f with
  | Constr.Const (k, _) -> Gradual.kind_of env k
  | _ -> None

let is_any env t = is_unknown_type env Evd.empty (EConstr.of_constr t)

let rec strip_lambdas c = match Constr.kind c with
  | Constr.Lambda (_, _, b) -> strip_lambdas b
  | _ -> c

(* [depth]: how many definitions are followed at most *)
let rec possible env ~depth ~made_in c =
  match Constr.kind c with
  | Constr.App (f, [|a; b; v|]) when gradual_kind env f = Some Gradual.GCast ->
    (* [env] is the global one: types that mention the variables of the
       term (a parameter [A]) are not known here *)
    let closed t = EConstr.Vars.closed0 Evd.empty (EConstr.of_constr t) in
    if not (closed a && closed b) then Anything
    else if not (is_any env b) then Anything
    else if is_any env a then possible env ~depth ~made_in v
    else Among [{ otype = a; made_in }]
  | Constr.Case (_, _, _, _, _, _, brs) ->
    Array.fold_left (fun acc (_, br) -> union acc (possible env ~depth ~made_in br)) (Among []) brs
  | Constr.LetIn (_, _, _, body) -> possible env ~depth ~made_in body
  | Constr.Cast (c, _, _) -> possible env ~depth ~made_in c
  | Constr.App (f, _) -> defined env ~depth f
  | Constr.Const _ -> defined env ~depth c
  | _ -> Anything

and defined env ~depth f = match Constr.kind f with
  | Constr.Const (cst, _) when depth > 0 && Option.is_empty (Gradual.kind_of env cst) ->
    begin match (Environ.lookup_constant cst env).Declarations.const_body with
      | Declarations.Def b -> possible env ~depth:(depth - 1) ~made_in:(Some cst) (strip_lambdas b)
      | _ -> Anything
    end
  | _ -> Anything

type may_fail = {
  env : Environ.env;       (* where the cast is *)
  value : Constr.t;        (* the [Any] *)
  target : Constr.types;   (* what it is used as *)
  failing : origin list;   (* what it may be, and the cast fails for *)
  fitting : origin list;   (* what it may be, and the cast is fine for *)
}

let casts_that_may_fail env body =
  if not (Gradual.enabled env) || uses env [] body = [] then [] else
  (* a warning: whatever it cannot follow, it does not report *)
  try
  let found = ref [] in
  let sigma = Evd.from_env env in
  let rec visit env c =
    (match Constr.kind c with
     | Constr.App (f, [|a; b; v|]) when gradual_kind env f = Some Gradual.GCast
                                     && is_any env a && not (is_any env b) && EConstr.Vars.closed0 Evd.empty (EConstr.of_constr b) ->
       begin match possible (Global.env ()) ~depth:8 ~made_in:None v with
         | Among origins ->
           let failing, fitting = List.partition (fun o ->
               not (consistent env sigma (EConstr.of_constr o.otype) (EConstr.of_constr b))) origins in
           if failing <> [] then found := { env; value = v; target = b; failing; fitting } :: !found
         | Anything -> ()
       end
     | _ -> ());
    Termops.fold_constr_with_full_binders env Evd.empty
      (fun d env -> EConstr.push_rel d env)
      (fun env () c -> visit env (EConstr.Unsafe.to_constr c))
      env () (EConstr.of_constr c)
  in
  visit env body;
  List.rev !found
  with e when CErrors.noncritical e -> []

