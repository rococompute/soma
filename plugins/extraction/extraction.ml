(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Util
open Names
open Term
open Constr
open Context
open Declarations
open Declareops
open Environ
open Reductionops
open Retyping
open Inductiveops
open Namegen
open Miniml
open Table
open Mlutil
open Context.Rel.Declaration
(*i*)

exception I of inductive_kind

(* A set of all fixpoint functions currently being extracted *)
let current_fixpoints = ref ([] : Constant.t list)

(* NB: In OCaml, [type_of] and [get_of] might raise
   [SingletonInductiveBecomeProp]. This exception will be caught
   in late wrappers around the exported functions of this file,
   in order to display the location of the issue. *)

let type_of env sg c =
  let polyprop = (lang() == Haskell) in
  Retyping.get_type_of ~polyprop env sg (Termops.strip_outer_cast sg c)

let sort_of env sg c =
  let polyprop = (lang() == Haskell) in
  Retyping.get_sort_quality_of ~polyprop env sg (Termops.strip_outer_cast sg c)

(*S Generation of flags and signatures. *)

(* The type [flag] gives us information about any Rocq term:
   \begin{itemize}
   \item [TypeScheme] denotes a type scheme, that is
     something that will become a type after enough applications.
     More formally, a type scheme has type $(x_1:X_1)\ldots(x_n:X_n)s$ with
     [s = Set], [Prop] or [Type]
   \item [Default] denotes the other cases. It may be inexact after
     instantiation. For example [(X:Type)X] is [Default] and may give [Set]
     after instantiation, which is rather [TypeScheme]
   \item [Logic] denotes a term of sort [Prop], or a type scheme on sort [Prop]
   \item [Info] is the opposite. The same example [(X:Type)X] shows
     that an [Info] term might in fact be [Logic] later on.
   \end{itemize} *)

type info = Logic | Info

type scheme = TypeScheme | Default

type flag = info * scheme

(*s [flag_of_type] transforms a type [t] into a [flag].
  Really important function. *)

let info_of_quality = let open Sorts.Quality in function
  | QConstant QSProp | QConstant QProp -> Logic
  | QConstant QType | QVar _ | QGlobal _ -> Info

let info_of_sort s = info_of_quality (Sorts.quality s)

let rec flag_of_type env sg t : flag =
  let t = whd_all env sg t in
  match EConstr.kind sg t with
    | Prod (x,t,c) -> flag_of_type (EConstr.push_rel (LocalAssum (x,t)) env) sg c
    | Sort s -> (info_of_sort (EConstr.ESorts.kind sg s),TypeScheme)
    | _ -> (info_of_quality (sort_of env sg t),Default)

(*s Two particular cases of [flag_of_type]. *)

let is_default env sg t = match flag_of_type env sg t with
| (Info, Default) -> true
| _ -> false

exception NotDefault of kill_reason

let check_default env sg t =
  match flag_of_type env sg t with
    | _,TypeScheme -> raise (NotDefault Ktype)
    | Logic,_ -> raise (NotDefault Kprop)
    | _ -> ()

let is_info_scheme env sg t = match flag_of_type env sg t with
| (Info, TypeScheme) -> true
| _ -> false

let push_rel_assum (n, t) env =
  EConstr.push_rel (LocalAssum (n, t)) env

let push_rels_assum assums =
  EConstr.push_rel_context (List.map (fun (x,t) -> LocalAssum (x,t)) assums)

let qmono uctx inst lconstr = match uctx with
| Monomorphic -> EConstr.of_constr lconstr
| Polymorphic uctx ->
  let inst = InfvInst.instantiate uctx inst in
  let lconstr = Vars.subst_instance_constr inst lconstr in
  EConstr.of_constr lconstr

let get_opaque uctx inst access c =
  qmono uctx inst (fst (Global.force_proof access c))

let applistc c args = EConstr.mkApp (c, Array.of_list args)

(* Same as [Environ.push_rec_types], but for [EConstr.t] *)
let push_rec_types (lna,typarray,_) env =
  let ctxt =
    Array.map2_i
      (fun i na t -> LocalAssum (na, EConstr.Vars.lift i t)) lna typarray
  in
  Array.fold_left (fun e assum -> EConstr.push_rel assum e) env ctxt

(* Same as [Termops.nb_lam], but for [EConstr.t] *)
let nb_lam sg c = List.length (fst (EConstr.decompose_lambda sg c))

(* Same as [Term.decompose_lambda_n] but for [EConstr.t] *)
let decompose_lambda_n sg n =
  let rec lamdec_rec l n c =
    if n <= 0 then l,c
    else match EConstr.kind sg c with
      | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) (n-1) c
      | Cast (c,_,_)     -> lamdec_rec l n c
      | _ -> raise Not_found
  in
  lamdec_rec [] n

(*s [type_sign] gernerates a signature aimed at treating a type application. *)

let rec type_sign env sg c =
  match EConstr.kind sg (whd_all env sg c) with
    | Prod (n,t,d) ->
        (if is_info_scheme env sg t then Keep else Kill Kprop)
        :: (type_sign (push_rel_assum (n,t) env) sg d)
    | _ -> []

let rec type_scheme_nb_args env sg c =
  match EConstr.kind sg (whd_all env sg c) with
    | Prod (n,t,d) ->
        let n = type_scheme_nb_args (push_rel_assum (n,t) env) sg d in
        if is_info_scheme env sg t then n+1 else n
    | _ -> 0

let type_scheme_nb_args' env c =
  type_scheme_nb_args env (Evd.from_env env) (EConstr.of_constr c)

let _ = Hook.set type_scheme_nb_args_hook type_scheme_nb_args'

(*s [type_sign_vl] does the same, plus a type var list. *)

(* When generating type variables, we avoid any ' in their names
   (otherwise this may cause a lexer conflict in ocaml with 'a').
   We also get rid of unicode characters. Anyway, since type variables
   are local, the created name is just a matter of taste...
   See also Bug #3227 *)

let make_typvar n vl =
  let id = id_of_name n in
  let id' =
    let s = Id.to_string id in
    if not (String.contains s '\'') && Unicode.is_basic_ascii s then id
    else id_of_name Anonymous
  in
  let vl = Id.Set.of_list vl in
  next_ident_away id' vl

let rec type_sign_vl env sg c =
  match EConstr.kind sg (whd_all env sg c) with
    | Prod (n,t,d) ->
        let s,vl = type_sign_vl (push_rel_assum (n,t) env) sg d in
        if not (is_info_scheme env sg t) then Kill Kprop::s, vl
        else Keep::s, (make_typvar n.binder_name vl) :: vl
    | _ -> [],[]

let rec nb_default_params env sg c =
  match EConstr.kind sg (whd_all env sg c) with
    | Prod (n,t,d) ->
        let n = nb_default_params (push_rel_assum (n,t) env) sg d in
        if is_default env sg t then n+1 else n
    | _ -> 0

(* Enriching a signature with implicit information *)

let sign_with_implicits r s nb_params =
  let implicits = implicits_of_global r in
  let rec add_impl i = function
    | [] -> []
    | Keep::s when Int.Set.mem i implicits ->
       Kill (Kimplicit (r,i)) :: add_impl (i+1) s
    | sign::s -> sign :: add_impl (i+1) s
  in
  add_impl (1+nb_params) s

(*S Management of type variable contexts. *)

(* A De Bruijn variable context (db) is a context for translating Rocq [Rel]
   into ML type [Tvar]. *)

(*s From a type signature toward a type variable context (db). *)

let db_from_sign s =
  let rec make i acc = function
    | [] -> acc
    | Keep :: l -> make (i+1) (i::acc) l
    | Kill _ :: l -> make i (0::acc) l
  in make 1 [] s

(*s Create a type variable context from indications taken from
  an inductive type (see just below). *)

let rec db_from_ind dbmap i =
  if Int.equal i 0 then []
  else (try Int.Map.find i dbmap with Not_found -> 0)::(db_from_ind dbmap (i-1))

(*s [parse_ind_args] builds a map: [i->j] iff the i-th Rocq argument
  of a constructor corresponds to the j-th type var of the ML inductive. *)

(* \begin{itemize}
   \item [si] : signature of the inductive
   \item [i] :  counter of Rocq args for [(I args)]
   \item [j] : counter of ML type vars
   \item [relmax] : total args number of the constructor
   \end{itemize} *)

let parse_ind_args si args relmax =
  let rec parse i j = function
    | [] -> Int.Map.empty
    | Kill _ :: s -> parse (i+1) j s
    | Keep :: s ->
      (match Constr.kind args.(i-1) with
         | Rel k -> Int.Map.add (relmax+1-k) j (parse (i+1) (j+1) s)
         | _ -> parse (i+1) (j+1) s)
  in parse 1 1 si

let relevance_of_projection_repr mip p =
  match mip.mind_record with
  | NotRecord | FakeRecord ->
    CErrors.anomaly ~label:"relevance_of_projection" Pp.(str "not a projection")
  | PrimRecord { relevances; _ } ->
    relevances.(Names.Projection.Repr.arg p)

(** Because of automatic unboxing the easy way [mk_def c] on the
   constant body of primitive projections doesn't work. We pretend
   that they are implemented by matches until someone figures out how
   to clean it up (test with #4710 when working on this). *)
let fake_match_projection env p =
  let ind = Projection.Repr.inductive p in
  let proj_arg = Projection.Repr.arg p in
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let u = UVars.make_abstract_instance (Declareops.inductive_polymorphic_context mib) in
  let indu = mkIndU (ind,u) in
  let ctx, paramslet =
    let ntypes = Declareops.mind_ntypes mib in
    let subst = List.init ntypes (fun i -> mkIndU ((fst ind, ntypes - i - 1), u)) in
    let (ctx, cty) = mip.mind_nf_lc.(0) in
    let cty = Term.it_mkProd_or_LetIn cty ctx in
    let rctx, _ = decompose_prod_decls (Vars.substl subst cty) in
    List.chop mip.mind_consnrealdecls.(0) rctx
  in
  let ci_pp_info = { style = LetStyle } in
  let ci = {
    ci_ind = ind;
    ci_npar = mib.mind_nparams;
    ci_cstr_ndecls = mip.mind_consnrealdecls;
    ci_cstr_nargs = mip.mind_consnrealargs;
    ci_pp_info;
  }
  in
  let relevance = relevance_of_projection_repr mip p in
  let x = match mip.mind_record with
    | NotRecord | FakeRecord -> assert false
    | PrimRecord { id; _ } ->
      make_annot (Name id) mip.mind_relevance
  in
  let indty = mkApp (indu, Context.Rel.instance mkRel 0 paramslet) in
  let rec fold arg j subst = function
    | [] -> assert false
    | LocalAssum (na,ty) :: rem ->
      let ty = Vars.substl subst (liftn 1 j ty) in
      if arg != proj_arg then
        let kn = Projection.Repr.make ind ~proj_npars:mib.mind_nparams ~proj_arg:arg in
        fold (arg+1) (j+1) (mkProj (Projection.make kn false, na.binder_relevance, mkRel 1)::subst) rem
      else
        let p = ([|x|], liftn 1 2 ty) in
        let branch =
          let nas = Array.of_list (List.rev_map Context.Rel.Declaration.get_annot ctx) in
          (nas, mkRel (List.length ctx - (j - 1)))
        in
        let params = Context.Rel.instance mkRel 1 paramslet in
        let body = mkCase (ci, u, params, (p,relevance), NoInvert, mkRel 1, [|branch|]) in
        it_mkLambda_or_LetIn (mkLambda (x,indty,body)) mib.mind_params_ctxt
    | LocalDef (_,c,t) :: rem ->
      let c = liftn 1 j c in
      let c1 = Vars.substl subst c in
      fold arg (j+1) (c1::subst) rem
  in
  fold 0 1 [] (List.rev ctx)

(*S Extraction of a type. *)

(* [extract_type env db c args] is used to produce an ML type from the
   coq term [(c args)], which is supposed to be a Rocq type. *)

(* [db] is a context for translating Rocq [Rel] into ML type [Tvar]. *)

(* [j] stands for the next ML type var. [j=0] means we do not
   generate ML type var anymore (in subterms for example). *)


let rec extract_type (table : Common.State.t) env sg db j c args =
  match EConstr.kind sg (whd_betaiotazeta env sg c) with
    | App (d, args') ->
        (* We just accumulate the arguments. *)
        extract_type table env sg db j d (Array.to_list args' @ args)
    | Lambda (_,_,d) ->
        (match args with
           | [] -> assert false (* A lambda cannot be a type. *)
           | a :: args -> extract_type table env sg db j (EConstr.Vars.subst1 a d) args)
    | Prod (n,t,d) ->
        assert (List.is_empty args);
        let env' = push_rel_assum (n,t) env in
        (match flag_of_type env sg t with
           | (Info, Default) ->
               (* Standard case: two [extract_type] ... *)
               let mld = extract_type table env' sg (0::db) j d [] in
               (match expand table env mld with
                  | Tdummy d -> Tdummy d
                  | _ -> Tarr (extract_type table env sg db 0 t [], mld))
           | (Info, TypeScheme) when j > 0 ->
               (* A new type var. *)
               let mld = extract_type table env' sg (j::db) (j+1) d [] in
               (match expand table env mld with
                  | Tdummy d -> Tdummy d
                  | _ -> Tarr (Tdummy Ktype, mld))
           | _,lvl ->
               let mld = extract_type table env' sg (0::db) j d [] in
               (match expand table env mld with
                  | Tdummy d -> Tdummy d
                  | _ ->
                      let reason = if lvl == TypeScheme then Ktype else Kprop in
                      Tarr (Tdummy reason, mld)))
    | Sort _ -> Tdummy Ktype (* The two logical cases. *)
    | _ when info_of_quality (sort_of env sg (applistc c args)) == Logic -> Tdummy Kprop
    | Rel n ->
        (match EConstr.lookup_rel n env with
           | LocalDef (_,t,_) ->
               extract_type table env sg db j (EConstr.Vars.lift n t) args
           | _ ->
               (* Asks [db] a translation for [n]. *)
               if n > List.length db then Tunknown
               else let n' = List.nth db (n-1) in
               if Int.equal n' 0 then Tunknown else Tvar n')
    | Const (kn,u) ->
        let inst = InfvInst.ground (EConstr.EInstance.kind sg u) in
        let r = { glob = GlobRef.ConstRef kn; inst } in
        let typ = type_of env sg (EConstr.mkConstU (kn,u)) in
        (match flag_of_type env sg typ with
           | (Logic,_) -> assert false (* Cf. logical cases above *)
           | (Info, TypeScheme) ->
             let mlt = extract_type_app table env sg db (r, type_sign env sg typ) args in
             mlt
           | (Info, Default) ->
               (* Not an ML type, for example [(c:forall X, X->X) Type nat] *)
               let cb = lookup_constant kn env in
               (match cb.const_body with
                 | Undef _  | OpaqueDef _ | Primitive _ | Symbol _ -> Tunknown (* Brutal approx ... *)
                  | Def lbody ->
                      (* We try to reduce. *)
                      let newc = applistc (qmono cb.const_universes inst lbody) args in
                      extract_type table env sg db j newc []))
    | Ind ((kn, i), u) ->
        let inst = InfvInst.ground (EConstr.EInstance.kind sg u) in
        let r = { glob = GlobRef.IndRef (kn, i); inst } in
        let s = (extract_ind table env kn inst).ind_packets.(i).ip_sign in
        extract_type_app table env sg db (r, s) args
    | Proj (p,r,t) ->
       (* Let's try to reduce, if it hasn't already been done. *)
       if Projection.unfolded p then Tunknown
       else
         extract_type table env sg db j (EConstr.mkProj (Projection.unfold p, r, t)) args
    | Case _ | Fix _ | CoFix _ -> Tunknown
    | Evar _ | Meta _ -> Taxiom (* only possible during Show Extraction *)
    | Var v ->
       (* For Show Extraction *)
       let open Context.Named.Declaration in
       (match EConstr.lookup_named v env with
        | LocalDef (_,body,_) ->
           extract_type table env sg db j (EConstr.applist (body,args)) []
        | LocalAssum (_,ty) ->
           let r = { glob = GlobRef.VarRef v; inst = InfvInst.empty } in
           (match flag_of_type env sg ty with
            | (Logic,_) -> assert false (* Cf. logical cases above *)
            | (Info, TypeScheme) ->
              extract_type_app table env sg db (r, type_sign env sg ty) args
            | (Info, Default) -> Tunknown))
    | Cast _ | LetIn _ | Construct _ | Int _ | Float _ | String _ | Array _ -> assert false

(*s Auxiliary function dealing with type application.
  Precondition: [r] is a type scheme represented by the signature [s],
  and is completely applied: [List.length args = List.length s]. *)

and extract_type_app table env sg db (r,s) args =
  let ml_args =
    List.fold_right
      (fun (b,c) a -> if b == Keep then
         let p = List.length (fst (whd_decompose_prod env sg (type_of env sg c))) in
         let db = iterate (fun l -> 0 :: l) p db in
         (extract_type_scheme table env sg db c p) :: a
       else a)
      (List.combine s args) []
  in Tglob (r, ml_args)

(*S Extraction of a type scheme. *)

(* [extract_type_scheme env db c p] works on a Rocq term [c] which is
  an informative type scheme. It means that [c] is not a Rocq type, but will
  be when applied to sufficiently many arguments ([p] in fact).
  This function decomposes p lambdas, with eta-expansion if needed. *)

(* [db] is a context for translating Rocq [Rel] into ML type [Tvar]. *)

and extract_type_scheme table env sg db c p =
  if Int.equal p 0 then extract_type table env sg db 0 c []
  else
    let c = whd_betaiotazeta env sg c in
    match EConstr.kind sg c with
      | Lambda (n,t,d) ->
          extract_type_scheme table (push_rel_assum (n,t) env) sg db d (p-1)
      | _ ->
          let rels = fst (whd_decompose_prod env sg (type_of env sg c)) in
          let env = push_rels_assum rels env in
          let eta_args = List.rev_map EConstr.mkRel (List.interval 1 p) in
          extract_type table env sg db 0 (EConstr.Vars.lift p c) eta_args


(*S Extraction of an inductive type. *)

(* First, a version with cache *)

and extract_ind table env kn inst = (* kn is supposed to be in long form *)
  let mib = Environ.lookup_mind kn env in
  match lookup_ind (Common.State.get_table table) kn inst mib with
  | Some ml_ind -> ml_ind
  | None ->
     try
       extract_really_ind table env kn inst mib
     with SingletonInductiveBecomesProp ind ->
       error_singleton_become_prop ind

(* Then the real function *)

and extract_really_ind table env kn inst mib =
    (* First, if this inductive is aliased via a Module,
       we process the original inductive if possible.
       When at toplevel of the monolithic case, we cannot do much
       (cf Vector and bug #2570) *)
    let equiv =
      if lang () != Ocaml ||
         (not (Common.State.get_modular table) && at_toplevel (MutInd.modpath kn)) ||
         KerName.equal (MutInd.canonical kn) (MutInd.user kn)
      then
        NoEquiv
      else
        begin
          ignore (extract_ind table env (MutInd.make1 (MutInd.canonical kn)) inst);
          Equiv (MutInd.canonical kn)
        end
    in
    let env, u = match mib.mind_universes with
    | Monomorphic -> env, UVars.Instance.empty
    | Polymorphic uctx ->
      (* FIXME: we should probably push the levels *)
      env, InfvInst.instantiate uctx inst
    in
    (* Everything concerning parameters. *)
    (* We do that first, since they are common to all the [mib]. *)
    let mip0 = mib.mind_packets.(0) in
    let ndecls = List.length mib.mind_params_ctxt in
    let npar = mib.mind_nparams in
    let epar = push_rel_context (Vars.subst_instance_context u mib.mind_params_ctxt) env in
    let sg = Evd.from_env env in
    (* First pass: we store inductive signatures together with *)
    (* their type var list. *)
    let packets =
      Array.mapi
        (fun i mip ->
           let ar = Inductive.type_of_inductive ((mib,mip),u) in
           let ar = EConstr.of_constr ar in
           let info = (fst (flag_of_type env sg ar) = Info) in
           let s,v = if info then type_sign_vl env sg ar else [],[] in
           let ncons = Array.length mip.mind_nf_lc in
           let t = Array.make ncons [] in
           { ip_typename = mip.mind_typename;
             ip_typename_ref = { glob = GlobRef.IndRef (kn, i); inst };
             ip_consnames = mip.mind_consnames;
             ip_consnames_ref = Array.init ncons (fun j -> { glob = GlobRef.ConstructRef ((kn, i), j + 1); inst });
             ip_logical = not info;
             ip_sign = s;
             ip_vars = v;
             ip_types = t }, u)
        mib.mind_packets
    in

    add_ind (Common.State.get_table table) kn inst mib
      {ind_kind = Standard;
       ind_nparams = npar;
       ind_packets = Array.map fst packets;
       ind_equiv = equiv
      };
    (* Second pass: we extract constructors *)
    let () = packets |> Array.iteri @@ fun i (p,u) ->
      if not p.ip_logical then
        let types = Inductive.arities_of_constructors ((kn,i),u) (mib, mib.mind_packets.(i)) in
        for j = 0 to Array.length types - 1 do
          let t = snd (decompose_prod_n_decls ndecls types.(j)) in
          let prods,head = Reduction.whd_decompose_prod epar t in
          let nprods = List.length prods in
          let args = match Constr.kind head with
            | App (f,args) -> args (* [Constr.kind f = Ind ip] *)
            | _ -> [||]
          in
          let dbmap = parse_ind_args p.ip_sign args (nprods + ndecls) in
          let db = db_from_ind dbmap ndecls in
          p.ip_types.(j) <-
            extract_type_cons table epar sg db dbmap (EConstr.of_constr t) (ndecls+1)
        done
    in
    (* Third pass: we determine special cases. *)
    let ind_info =
      try
        let ip = (kn, 0) in
        let r = { glob = GlobRef.IndRef ip; inst } in
        if is_custom r then raise (I Standard);
        if mib.mind_finite == CoFinite then raise (I Coinductive);
        if not (Int.equal (Declareops.mind_ntypes mib) 1) then raise (I Standard);
        let p,u = packets.(0) in
        if p.ip_logical then raise (I Standard);
        if not (Int.equal (Array.length p.ip_types) 1) then raise (I Standard);
        let typ = p.ip_types.(0) in
        let gcstr = p.ip_consnames_ref.(0) in
        let l = if conservative_types () then [] else
          filter_extracted_constructor_types table env npar gcstr typ
        in
        if List.is_empty l then raise (I Standard);
        if mip0.mind_record == Declarations.NotRecord then
          if not (keep_singleton ()) && Int.equal (List.length l) 1 && not (type_mem_kn kn (List.hd l))
          then raise (I Singleton)
          else raise (I Standard);
        (* Now we're sure it's a record. *)
        (* First, we find its field names. *)
        let rec names_prod t = match Constr.kind t with
          | Prod(n,_,t) -> n::(names_prod t)
          | LetIn(_,_,_,t) -> names_prod t
          | Cast(t,_,_) -> names_prod t
          | _ -> []
        in
        let field_names =
          List.skipn mib.mind_nparams (names_prod mip0.mind_user_lc.(0)) in
        assert (Int.equal (List.length field_names) (List.length typ));
        let mp = MutInd.modpath kn in
        let implicits = implicits_of_global gcstr in
        let ty = Inductive.type_of_inductive ((mib,mip0),u) in
        let nparams = nb_default_params env sg (EConstr.of_constr ty) in
        let rec select_fields i l typs = match l,typs with
          | [],[] -> []
          | _::l, typ::typs when isTdummy (expand table env typ) || Int.Set.mem i implicits ->
              select_fields (i+1) l typs
          | {binder_name=Anonymous}::l, typ::typs ->
              None :: (select_fields (i+1) l typs)
          | {binder_name=Name id}::l, typ::typs ->
              let knp = Constant.make2 mp id in
              (* Is it safe to use [id] for projections [foo.id] ? *)
              if List.for_all ((==) Keep) (type2signature table env typ)
              then (* for OCaml inlining: *) add_projection (Common.State.get_table table) nparams knp ip;
              Some { glob = GlobRef.ConstRef knp; inst } :: (select_fields (i+1) l typs)
          | _ -> assert false
        in
        let field_glob = select_fields (1+npar) field_names typ in
        if not (keep_singleton ()) && Int.equal (List.length l) 1 && not (type_mem_kn kn (List.hd l))
        then Singleton (* in passing, we registered the (identity) projection *)
        else Record field_glob
      with (I info) -> info
    in
    let i = {ind_kind = ind_info;
             ind_nparams = npar;
             ind_packets = Array.map fst packets;
             ind_equiv = equiv }
    in
    add_ind (Common.State.get_table table) kn inst mib i;
    add_inductive_kind (Common.State.get_table table) kn inst i.ind_kind;
    i

(*s [extract_type_cons] extracts the type of an inductive
  constructor toward the corresponding list of ML types.

   - [db] is a context for translating Rocq [Rel] into ML type [Tvar]
   - [dbmap] is a translation map (produced by a call to [parse_in_args])
   - [i] is the rank of the current product (initially [params_nb+1])
*)

and extract_type_cons table env sg db dbmap c i =
  match EConstr.kind sg (whd_all env sg c) with
    | Prod (n,t,d) ->
        let env' = push_rel_assum (n,t) env in
        let db' = (try Int.Map.find i dbmap with Not_found -> 0) :: db in
        let l = extract_type_cons table env' sg db' dbmap d (i+1) in
        (extract_type table env sg db 0 t []) :: l
    | _ -> []

(*s Recording the ML type abbreviation of a Rocq type scheme constant. *)

and mlt_env table env r = let open GlobRef in match r.glob with
  | IndRef _ | ConstructRef _ | VarRef _ -> None
  | ConstRef kn ->
     let cb = Environ.lookup_constant kn env in
     match cb.const_body with
     | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> None
     | Def l_body ->
        match lookup_typedef (Common.State.get_table table) kn r.inst cb with
        | Some _ as o -> o
        | None ->
           let sg = Evd.from_env env in
           let typ = EConstr.of_constr cb.const_type
           (* FIXME not sure if we should instantiate univs here *) in
           match flag_of_type env sg typ with
           | Info,TypeScheme ->
              let body = qmono cb.const_universes r.inst l_body in
              let s = type_sign env sg typ in
              let db = db_from_sign s in
              let t = extract_type_scheme table env sg db body (List.length s)
              in add_typedef (Common.State.get_table table) kn r.inst cb t; Some t
           | _ -> None

and expand table env = type_expand (mlt_env table env)
(* Filter constructor arguments that are removed from the extracted type.
   [ind_nparams] accounts for the inductive parameters in constructor
   argument numbers used by [Extraction Implicit]. *)
and filter_extracted_constructor_types table env ind_nparams r types =
  let implicits = implicits_of_global r in
  let rec filter i = function
    | [] -> []
    | t::l ->
        let l' = filter (succ i) l in
        if isTdummy (expand table env t) || Int.Set.mem i implicits then l'
        else t::l'
  in filter (1+ind_nparams) types
and type2signature table env = type_to_signature (mlt_env table env)
let type2sign table env = type_to_sign (mlt_env table env)
let type_expunge table env = type_expunge (mlt_env table env)
let type_expunge_from_sign table env = type_expunge_from_sign (mlt_env table env)

(*s Extraction of the type of a constant. *)

(*s Type parameters passed at run time, for gradual casts.

   Casts need the runtime description of their types (see [extract_gradual]
   below). When they mention a type parameter of a constant, the constant
   takes that description as an argument instead of erasing it, and its
   callers pass it. A parameter is needed when it occurs in the types of a
   cast, [unknown] or [err], or in an argument given to a needed parameter
   of another function. Other type parameters are erased as usual, so code
   without casts is extracted as before. *)

(* Part of the state: backtracking may give a name to a different
   constant. *)
let gradual_params_cache = Summary.ref ~name:"ExtrGradualParams" Cmap_env.empty

(* De Bruijn levels: a binder introduced at depth [l] (the number of
   binders above it) has level [l], and [Rel m] at depth [d] refers to
   level [d - m]. *)

(* [whd_all], when [t] is closed: the analysis does not track the types of
   local variables. *)
let gradual_whd env sg t =
  if EConstr.Vars.closed0 sg t then whd_all env sg t else t

(* The positions, in the product spine of [typ], of the parameters of [t]
   needed at run time. [heads] maps the levels of local fixpoints to the
   parameters they need; [lvl] is the depth of [t]. *)
let rec gradual_needed_params env sg heads lvl t typ =
  let rec spine env typ acc =
    match EConstr.kind sg (gradual_whd env sg typ) with
    | Prod (na, a, b) ->
      let is_type = EConstr.isSort sg (gradual_whd env sg a) in
      spine (EConstr.push_rel (LocalAssum (na, a)) env) b (is_type :: acc)
    | _ -> List.rev acc
  in
  let params = spine env typ [] in
  let k = List.length params in
  if not (List.mem true params) then Int.Set.empty
  else
    (* eta-expand [t] to [k] lambdas, and take their body *)
    let ctx, body = EConstr.decompose_lambda sg t in
    let m = List.length ctx in
    let body =
      if m >= k then EConstr.it_mkLambda body (List.firstn (m - k) ctx)
      else
        EConstr.mkApp (EConstr.Vars.lift (k - m) body,
                       Array.init (k - m) (fun i -> EConstr.mkRel (k - m - i)))
    in
    List.fold_left_i (fun j acc is_type ->
        if is_type && gradual_needs_rel env sg heads (lvl + k) (k - j) body
        then Int.Set.add j acc else acc) 0 Int.Set.empty params

(* Does [Rel n] occur in [t], at depth [lvl], where its runtime description
   is needed? *)
and gradual_needs_rel env sg heads lvl n t =
  let rec go heads d t =
    let occurs a = not (EConstr.Vars.noccurn sg (n + d) a) in
    match EConstr.kind sg t with
    | App (f, args) ->
      let needed = match EConstr.kind sg f with
        | Const (c, _) ->
          begin match Gradual.kind_of env c with
            | Some k -> Int.Set.of_list (List.init (Gradual.arity k - 1) (fun i -> i))
            | None -> gradual_const_params env c
          end
        | Rel m ->
          begin match Int.Map.find_opt (lvl + d - m) heads with
            | Some r -> !r
            | None -> Int.Set.empty
          end
        | Fix ((_, i), recd) ->
          let refs, _ = gradual_fix_params env sg heads (lvl + d) recd in
          !(refs.(i))
        | _ -> Int.Set.empty
      in
      let rec needed_arg i =
        i < Array.length args
        && ((Int.Set.mem i needed && occurs args.(i)) || needed_arg (i + 1))
      in
      needed_arg 0 || go heads d f || Array.exists (go heads d) args
    | Fix (_, ((_, tys, bodies) as recd)) | CoFix (_, ((_, tys, bodies) as recd)) ->
      let nb = Array.length bodies in
      let _, heads' = gradual_fix_params env sg heads (lvl + d) recd in
      Array.exists (go heads d) tys || Array.exists (go heads' (d + nb)) bodies
    | _ -> EConstr.fold_with_binders sg succ (fun d acc t -> acc || go heads d t) d false t
  in
  go heads 0 t

(* The parameters needed by the functions of a block of (co)fixpoints at
   depth [lvl], computed by iteration, and [heads] extended with them. *)
and gradual_fix_params env sg heads lvl (_, tys, bodies) =
  let nb = Array.length bodies in
  let refs = Array.map (fun _ -> ref Int.Set.empty) bodies in
  let heads = Array.fold_left_i (fun i h r -> Int.Map.add (lvl + i) r h) heads refs in
  let rec iterate () =
    let changed = ref false in
    Array.iteri (fun i b ->
        let s = gradual_needed_params env sg heads (lvl + nb) b
            (EConstr.Vars.lift nb tys.(i)) in
        if not (Int.Set.equal s !(refs.(i))) then (refs.(i) := s; changed := true))
      bodies;
    if !changed then iterate ()
  in
  iterate ();
  refs, heads

and gradual_const_params env c =
  match Cmap_env.find_opt c !gradual_params_cache with
  | Some s -> s
  | None ->
    let cb = lookup_constant c env in
    let s = match cb.const_body with
      | Def b when Option.is_empty (Structures.PrimitiveProjections.find_opt c) ->
        let sg = Evd.from_env env in
        gradual_needed_params env sg Int.Map.empty 0
          (EConstr.of_constr b) (EConstr.of_constr cb.const_type)
      | _ -> Int.Set.empty
    in
    gradual_params_cache := Cmap_env.add c s !gradual_params_cache;
    s

let gradual_type_params env kn =
  if Option.has_some (Gradual.get env Gradual.GCast) then gradual_const_params env kn
  else Int.Set.empty

(* The ML type of a constant keeps the needed type parameters. *)
let gradual_keep_params table env kn mlt =
  let needed = gradual_type_params env kn in
  if Int.Set.is_empty needed then mlt
  else
    let rec keep j = function
      | Tarr (Tdummy Ktype, t) when Int.Set.mem j needed -> Tarr (Tunknown, keep (j + 1) t)
      | Tarr (a, t) -> Tarr (a, keep (j + 1) t)
      | t -> t
    in
    keep 0 (expand table env mlt)

let record_constant_type table env sg kn inst opt_typ =
  let cb = lookup_constant kn env in
  match lookup_cst_type (Common.State.get_table table) kn inst cb with
  | Some schema -> schema
  | None ->
     let typ = match opt_typ with
       | None -> qmono cb.const_universes inst cb.const_type
       | Some typ -> typ
     in
     let mlt = extract_type table env sg [] 1 typ [] in
     let mlt = gradual_keep_params table env kn mlt in
     let schema = (type_maxvar mlt, mlt) in
     let () = add_cst_type (Common.State.get_table table) kn inst cb schema in
     schema

(*S Extraction of a term. *)

(*S Gradual casts. *)

(* Extraction erases types, so a cast [cast A B t] of gradual Rocq (GCIC^G,
   see kernel/gradual.ml) is extracted to a call to the runtime [Gradual_rt]
   (gradual_rt.ml) with runtime descriptions of [A] and [B]. For each
   inductive type in a description, we generate a function that rebuilds its
   constructors at another instance of the type, casting their arguments.
   Type variables have a runtime description when they are parameters of
   inductive types (in these functions) or of the constant being extracted
   (see [gradual_keep_params]); casts at other type variables are
   rejected. *)

let rt name = MLraw ("Gradual_rt." ^ name)
let rt_app name args = MLapp (rt name, args)
let rt_list l = List.fold_right (fun a l -> rt_app "acons" [a; l]) l (rt "anil")

(* What a Rocq variable is at run time, while building descriptions. The
   functions give the ML expression at a given ML depth (see [rt_var]). *)
type rt_binding =
  | RtTy of (int -> ml_ast)  (* a type: its runtime description *)
  | RtVal of (int -> ml_ast) (* a value *)
  | RtNone                   (* a type or a proof without runtime counterpart *)
  | RtMissing                (* a value without runtime counterpart *)

type rt_ctx = {
  rt_env : env;       (* [rt_outer] extended with [rt_binders] *)
  rt_outer : env;     (* environment of the term being extracted *)
  rt_mle : Mlenv.t;   (* and its ML environment *)
  rt_binders : (EConstr.rel_declaration * rt_binding) list; (* innermost first *)
  rt_depth : int;     (* number of ML binders introduced since [rt_outer] *)
  rt_needed : (inductive * EConstr.EInstance.t) list ref;
  (* inductive types whose cast function the runtime will need *)
}

(* The ML variable introduced at depth [l], seen at depth [d]. *)
let rt_var l d = MLrel (d - l + 1)

let rt_push_ml ctx = { ctx with rt_depth = ctx.rt_depth + 1 }, ctx.rt_depth + 1

let rt_push ctx decl b =
  { ctx with rt_env = EConstr.push_rel decl ctx.rt_env;
             rt_binders = (decl, b) :: ctx.rt_binders }

let gradual_ctx env mle =
  { rt_env = env; rt_outer = env; rt_mle = mle; rt_binders = [];
    rt_depth = 0; rt_needed = ref [] }

let gradual_error env sg msg t =
  CErrors.user_err
    Pp.(str "Cannot extract a gradual cast: " ++ msg ++ str ":" ++
        brk (1, 2) ++ Printer.pr_econstr_env env sg t ++ str ".")

let gradual_kind_of_term env sg t =
  let f = match EConstr.kind sg t with App (f, _) -> f | _ -> t in
  match EConstr.kind sg f with
  | Const (c, _) -> Gradual.kind_of env c
  | _ -> None

(* The name of an inductive type at run time, as an OCaml string literal. *)
let gradual_ind_name_ml env ind =
  let mib = lookup_mind (fst ind) env in
  let kn = KerName.to_string (MutInd.canonical (fst ind)) in
  let name =
    if Int.equal (Array.length mib.mind_packets) 1 then kn
    else kn ^ "#" ^ Id.to_string mib.mind_packets.(snd ind).mind_typename
  in
  MLraw ("\"" ^ String.escaped name ^ "\"")

(* Precondition: [(c args)] is not a type scheme, and is informative. *)

(* [mle] is a ML environment [Mlenv.t]. *)
(* [mlt] is the ML type we want our extraction of [(c args)] to have. *)

let rec extract_term table env sg mle mlt c args =
  match EConstr.kind sg c with
    | App (f,a) ->
       extract_term table env sg mle mlt f (Array.to_list a @ args)
    | Lambda (n, t, d) ->
      let id = map_annot id_of_name n in
      let idna = map_annot Name.mk_name id in
        (match args with
           | a :: l ->
               (* We make as many [LetIn] as possible. *)
               let l' = List.map (EConstr.Vars.lift 1) l in
               let d' = EConstr.mkLetIn (idna,a,t,applistc d l') in
               extract_term table env sg mle mlt d' []
           | [] ->
               let env' = push_rel_assum (idna, t) env in
               let id, a =
                 try check_default env sg t; Id id.binder_name, new_meta()
                 with NotDefault d -> Dummy, Tdummy d
               in
               let b = new_meta () in
               (* If [mlt] cannot be unified with an arrow type, then magic! *)
               let magic = needs_magic (mlt, Tarr (a, b)) in
               let d' = extract_term table env' sg (Mlenv.push_type mle a) b d [] in
               put_magic_if magic (MLlam (id, d')))
    | LetIn (n, c1, t1, c2) ->
        let id = map_annot id_of_name n in
        let env' = EConstr.push_rel (LocalDef (map_annot Name.mk_name id, c1, t1)) env in
        (* We directly push the args inside the [LetIn].
           TODO: the opt_let_app flag is supposed to prevent that *)
        let args' = List.map (EConstr.Vars.lift 1) args in
        (try
          check_default env sg t1;
          let a = new_meta () in
          let c1' = extract_term table env sg mle a c1 [] in
          (* The type of [c1'] is generalized and stored in [mle]. *)
          let mle' =
            if generalizable c1'
            then Mlenv.push_gen mle a
            else Mlenv.push_type mle a
          in
          MLletin (Id id.binder_name, c1', extract_term table env' sg mle' mlt c2 args')
        with NotDefault d ->
          let mle' = Mlenv.push_std_type mle (Tdummy d) in
          ast_pop (extract_term table env' sg mle' mlt c2 args'))
    | Const (kn,u) ->
        begin match Gradual.kind_of env kn with
        | Some k when not (is_custom { glob = GlobRef.ConstRef kn; inst = InfvInst.empty }) ->
          extract_gradual table env sg mle mlt k (kn, u) args
        | _ -> extract_cst_app table env sg mle mlt (kn, u) args
        end
    | Construct (cp,u) ->
        extract_cons_app table env sg mle mlt (cp, u) args
    | Proj (p, _, c) ->
        let p = Projection.repr p in
        let term = fake_match_projection env p in
        let ind = Inductiveops.find_rectype env sg (Retyping.get_type_of env sg c) in
        let indf,_ = Inductiveops.dest_ind_type ind in
        let _,indargs = Inductiveops.dest_ind_family indf in
        extract_term table env sg mle mlt (beta_applist sg (EConstr.of_constr term,indargs@[c])) args
    | Rel n ->
        (* As soon as the expected [mlt] for the head is known, *)
        (* we unify it with an fresh copy of the stored type of [Rel n]. *)
        let extract_rel mlt = put_magic (mlt, Mlenv.get mle n) (MLrel n)
        in extract_app table env sg mle mlt extract_rel args
    | Case (ci, u, pms, r, iv, c0, br) ->
        (* If invert_case then this is a match that will get erased later, but right now we don't care. *)
        (* the type of the match, for gradual elimination (see [extract_case]) *)
        let rty =
          if Option.has_some (Gradual.get env Gradual.GCast) then Some (type_of env sg c) else None
        in
        let (ip, r, iv, c0, br) = EConstr.expand_case env sg (ci, u, pms, r, iv, c0, br) in
        let ip = ci.ci_ind in
        extract_app table env sg mle mlt (extract_case ?rty table env sg mle (ip, u, c0, br)) args
    | Fix ((_,i),recd) ->
        extract_app table env sg mle mlt (extract_fix table env sg mle i recd) args
    | CoFix (i,recd) ->
        extract_app table env sg mle mlt (extract_fix table env sg mle i recd) args
    | Cast (c,_,_) -> extract_term table env sg mle mlt c args
    | Evar _ | Meta _ -> MLaxiom "evar"
    | Var v ->
       (* Only during Show Extraction *)
       let ty = Context.Named.Declaration.get_type @@ EConstr.lookup_named v env in
       let vty = extract_type table env sg [] 0 ty [] in
       let r = { glob = GlobRef.VarRef v; inst = InfvInst.empty } in
       let extract_var mlt = put_magic (mlt,vty) (MLglob r) in
       extract_app table env sg mle mlt extract_var args
    | Int i -> assert (args = []); MLuint i
    | Float f -> assert (args = []); MLfloat f
    | String s -> assert (args = []); MLstring s
    | Array (_u,t,def,_ty) ->
      assert (args = []);
      let a = new_meta () in
      let ml_arr = Array.map (fun c -> extract_term table env sg mle a c []) t in
      let def = extract_term table env sg mle a def [] in
      MLparray(ml_arr, def)
    | Ind _ | Prod _ | Sort _ -> assert false

(*s [extract_maybe_term] is [extract_term] for usual terms, else [MLdummy] *)

and extract_maybe_term table env sg mle mlt c =
  try check_default env sg (type_of env sg c);
    extract_term table env sg mle mlt c []
  with NotDefault d ->
    put_magic (mlt, Tdummy d) (MLdummy d)

(*s Generic way to deal with an application. *)

(* We first type all arguments starting with unknown meta types.
   This gives us the expected type of the head. Then we use the
   [mk_head] to produce the ML head from this type. *)

and extract_app table env sg mle mlt mk_head args =
  let metas = List.map new_meta args in
  let type_head = type_recomp (metas, mlt) in
  let mlargs = List.map2 (extract_maybe_term table env sg mle) metas args in
  mlapp (mk_head type_head) mlargs

(*s Auxiliary function used to extract arguments of constant or constructor. *)

and make_mlargs ?(types=Int.Set.empty) table env sg e s args typs =
  (* [types]: positions of type arguments passed at run time *)
  let arg i t a =
    if Int.Set.mem i types then MLmagic (gradual_reify table sg (gradual_ctx env e) a)
    else extract_maybe_term table env sg e t a
  in
  let rec f i = function
    | [], [], _ -> []
    | a::la, t::lt, [] -> arg i t a :: (f (i+1) (la,lt,[]))
    | a::la, t::lt, Keep::s -> arg i t a :: (f (i+1) (la,lt,s))
    | _::la, _::lt, _::s -> f (i+1) (la,lt,s)
    | _ -> assert false
  in f 0 (args,typs,s)

(*s Extraction of a constant applied to arguments. *)

and extract_cst_app table env sg mle mlt (kn, u) args =
  let inst = InfvInst.ground (EConstr.EInstance.kind sg u) in
  (* First, the [ml_schema] of the constant, in expanded version. *)
  let nb, t = record_constant_type table env sg kn inst None in
  let schema = nb, expand table env t in
  (* Can we instantiate types variables for this constant ? *)
  (* In Ocaml, inside the definition of this constant, the answer is no. *)
  let instantiated =
    if lang () == Ocaml && List.exists (fun c -> Constant.UserOrd.equal kn c) !current_fixpoints
    then var2var' (snd schema)
    else instantiation schema
  in
  (* Then the expected type of this constant. *)
  let a = new_meta () in
  (* We compare stored and expected types in two steps. *)
  (* First, can [kn] be applied to all args ? *)
  let metas = List.map new_meta args in
  let magic1 = needs_magic (type_recomp (metas, a), instantiated) in
  (* Second, is the resulting type compatible with the expected type [mlt] ? *)
  let magic2 = needs_magic (a, mlt) in
  (* The internal head receives a magic if [magic1] *)
  let r = { glob = GlobRef.ConstRef kn; inst } in
  let head = put_magic_if magic1 (MLglob r) in
  (* Now, the extraction of the arguments. *)
  let s_full = type2signature table env (snd schema) in
  let s_full = sign_with_implicits r s_full 0 in
  let s = sign_no_final_keeps s_full in
  let ls = List.length s in
  let la = List.length args in
  (* Type parameters passed at run time must be given: callers that do not
     know [kn] would not pass them. *)
  let types = gradual_type_params env kn in
  if not (Int.Set.is_empty types) && la <= Int.Set.max_elt types then
    gradual_error env sg
      (Pp.str "a function taking type parameters at run time is not applied to them")
      (applistc (EConstr.mkConstU (kn, u)) args);
  (* The ml arguments, already expunged from known logical ones *)
  let mla = make_mlargs ~types table env sg mle s args metas in
  (* For strict languages, purely logical signatures lead to a dummy lam
     (except when [Kill Ktype] everywhere). So a [MLdummy] is left
     accordingly. *)
  let optdummy = match sign_kind s_full with
    | UnsafeLogicalSig when lang () != Haskell -> [MLdummy Kprop]
    | _ -> []
  in
  (* Different situations depending of the number of arguments: *)
  if la >= ls
  then
    (* Enough args, cleanup already done in [mla], we only add the
       additional dummy if needed. *)
    put_magic_if (magic2 && not magic1) (mlapp head (optdummy @ mla))
  else
    (* Partially applied function with some logical arg missing.
       We complete via eta and expunge logical args. *)
    let ls' = ls-la in
    let s' = List.skipn la s in
    let mla = (List.map (ast_lift ls') mla) @ (eta_args_sign ls' s') in
    let e = anonym_or_dummy_lams (mlapp head mla) s' in
    put_magic_if magic2 (remove_n_lams (List.length optdummy) e)

(*s Extraction of an inductive constructor applied to arguments. *)

(* \begin{itemize}
   \item In ML, constructor arguments are uncurryfied.
   \item We managed to suppress logical parts inside inductive definitions,
   but they must appears outside (for partial applications for instance)
   \item We also suppressed all Rocq parameters to the inductives, since
   they are fixed, and thus are not used for the computation.
   \end{itemize} *)

and extract_cons_app table env sg mle mlt (cp, u) args =
  let ((kn, i) as ip, j) = cp in
  (* First, we build the type of the constructor, stored in small pieces. *)
  let inst = InfvInst.ground (EConstr.EInstance.kind sg u) in
  let mi = extract_ind table env kn inst in
  let params_nb = mi.ind_nparams in
  let oi = mi.ind_packets.(i) in
  let nb_tvars = List.length oi.ip_vars
  and types = List.map (expand table env) oi.ip_types.(j-1) in
  let list_tvar = List.map (fun i -> Tvar i) (List.interval 1 nb_tvars) in
  let gind = { glob = GlobRef.IndRef ip; inst } in
  let gcstr = { glob = GlobRef.ConstructRef cp; inst } in
  let type_cons = type_recomp (types, Tglob (gind, list_tvar)) in
  let type_cons = instantiation (nb_tvars, type_cons) in
  (* Then, the usual variables [s], [ls], [la], ... *)
  let s = List.map (type2sign table env) types in
  let s = sign_with_implicits gcstr s params_nb in
  let ls = List.length s in
  let la = List.length args in
  assert (la <= ls + params_nb);
  let la' = max 0 (la - params_nb) in
  let args' = List.lastn la' args in
  (* Now, we build the expected type of the constructor *)
  let metas = List.map new_meta args' in
  (* If stored and expected types differ, then magic! *)
  let a = new_meta () in
  let magic1 = needs_magic (type_cons, type_recomp (metas, a)) in
  let magic2 = needs_magic (a, mlt) in
  let head mla =
    if mi.ind_kind == Singleton then
      put_magic_if magic1 (List.hd mla) (* assert (List.length mla = 1) *)
    else
      let typeargs = match snd (type_decomp type_cons) with
        | Tglob (_,l) -> List.map type_simpl l
        | _ -> assert false
      in
      let typ = Tglob (gind, typeargs) in
      put_magic_if magic1 (MLcons (typ, gcstr, mla))
  in
  (* Different situations depending of the number of arguments: *)
  if la < params_nb then
    let head' = head (eta_args_sign ls s) in
    put_magic_if magic2
      (dummy_lams (anonym_or_dummy_lams head' s) (params_nb - la))
  else
    let mla = make_mlargs table env sg mle s args' metas in
    if Int.equal la (ls + params_nb)
    then put_magic_if (magic2 && not magic1) (head mla)
    else (* [ params_nb <= la <= ls + params_nb ] *)
      let ls' = params_nb + ls - la in
      let s' = List.lastn ls' s in
      let mla = (List.map (ast_lift ls') mla) @ (eta_args_sign ls' s') in
      put_magic_if magic2 (anonym_or_dummy_lams (head mla) s')

(*S Extraction of a case. *)

and extract_case ?rty table env sg mle ((kn,i) as ip, u, c, br) mlt =
  (* Native library programs become executable thunks and entries become
     their results. Their logical constructors are not a native data layout
     that an extracted consumer may inspect. *)
  (* [br]: bodies of each branch (in functional form) *)
  (* [ni]: number of arguments without parameters in each branch *)
  let ni = constructors_nrealargs env ip in
  let br_size = Array.length br in
  let inst = InfvInst.ground (EConstr.EInstance.kind sg u) in
  let gind = { glob = GlobRef.IndRef ip; inst } in
  if lang () == Ocaml && is_custom gind && List.exists (fun name ->
      Rocqlib.has_ref name &&
      GlobRef.CanOrd.equal (Rocqlib.lib_ref name) gind.glob)
      ["soma.native.program"; "soma.native.entry"; "soma.native.callback"; "soma.native.handle"; "soma.native.vector"; "soma.native.text_buffer"; "soma.native.table"] then
    CErrors.user_err Pp.(str "Native programs and entry points cannot be inspected by extracted code.");
  assert (Int.equal (Array.length ni) br_size);
  if Int.equal br_size 0 then begin
    add_recursors (Common.State.get_table table) env kn; (* May have passed unseen if logical ... *)
    MLexn "absurd case"
  end else
    (* [c] has an inductive type, and is not a type scheme type. *)
    let t = type_of env sg c in
    (* The only non-informative case: [c] is of sort [Prop]/[SProp] *)
    if info_of_quality (sort_of env sg t) == Logic then
      begin
        add_recursors (Common.State.get_table table) env kn; (* May have passed unseen if logical ... *)
        (* Logical singleton case: *)
        (* [match c with C i j k -> t] becomes [t'] *)
        assert (Int.equal br_size 1);
        let s = iterate (fun l -> Kill Kprop :: l) ni.(0) [] in
        let mlt = iterate (fun t -> Tarr (Tdummy Kprop, t)) ni.(0) mlt in
        let e = extract_maybe_term table env sg mle mlt br.(0) in
        snd (case_expunge s e)
      end
    else
      let mi = extract_ind table env kn inst in
      let oi = mi.ind_packets.(i) in
      let metas = Array.init (List.length oi.ip_vars) new_meta in
      (* The extraction of the head. *)
      let type_head = Tglob (gind, Array.to_list metas) in
      let a = extract_term table env sg mle type_head c [] in
      (* The extraction of each branch. *)
      let extract_branch i =
        let r = { glob = GlobRef.ConstructRef (ip, i + 1); inst } in
        (* The types of the arguments of the corresponding constructor. *)
        let f t = type_subst_vect metas (expand table env t) in
        let l = List.map f oi.ip_types.(i) in
        (* the corresponding signature *)
        let s = List.map (type2sign table env) oi.ip_types.(i) in
        let s = sign_with_implicits r s mi.ind_nparams in
        (* Extraction of the branch (in functional form). *)
        let e = extract_maybe_term table env sg mle (type_recomp (l,mlt)) br.(i) in
        (* We suppress dummy arguments according to signature. *)
        let ids,e = case_expunge s e in
        (List.rev ids, Pusual r, e)
      in
      if mi.ind_kind == Singleton then
        begin
          (* Informative singleton case: *)
          (* [match c with C i -> t] becomes [let i = c' in t'] *)
          assert (Int.equal br_size 1);
          let (ids,_,e') = extract_branch 0 in
          assert (Int.equal (List.length ids) 1);
          MLletin (tmp_id (List.hd ids),a,e')
        end
      else
        (* Standard case: we apply [extract_branch]. *)
        let typs = List.map type_simpl (Array.to_list metas) in
        let typ = Tglob (gind, typs) in
        let case = MLcase (typ, a, Array.init br_size extract_branch) in
        (* Gradual casts: as in the kernel, matching on [?] or [err] gives
           [?] or [err] at the type of the match [rty], when the values of
           the scrutinee's type can be them and [rty] has a runtime
           description; otherwise matching on them raises (see
           [Extract_env.gradual_guard_cases]). *)
        match rty with
        | Some rty when gradual_ind_holds_exc table env ip u ->
          let ty =
            try Some (gradual_reify table sg (gradual_ctx env mle) rty)
            with e when CErrors.noncritical e -> None
          in
          (* [let x = a in if is_exc x then propagate ty x else match x with ...]:
             the description is only built when [x] is [?] or [err] *)
          begin match ty, ast_lift 1 case with
            | Some ty, MLcase (typ, _, br) ->
              MLletin (Id (Id.of_string "x"), a,
                       MLif (rt_app "is_exc_value" [MLrel 1],
                             MLmagic (rt_app "propagate" [ast_lift 1 ty; MLrel 1]),
                             MLcase (typ, MLrel 1, br)))
            | _ -> case
          end
        | _ -> case

(*s Extraction of a (co)-fixpoint. *)

and extract_fix table env sg mle i (fi,ti,ci as recd) mlt =
  let env = push_rec_types recd env in
  let metas = Array.map new_meta fi in
  metas.(i) <- mlt;
  let mle = Array.fold_left Mlenv.push_type mle metas in
  let ei = Array.map2 (extract_maybe_term table env sg mle) metas ci in
  MLfix (i, Array.map (fun x -> id_of_name x.binder_name) fi, ei)

(*s Extraction of [cast A B t], [unknown A] and [err A], applied to [args]. *)

and extract_gradual table env sg mle mlt kind (kn, u) args =
  let needed = Gradual.arity kind in
  let la = List.length args in
  if la < needed then
    (* Partial application: eta-expand. *)
    let rec eta env n c ty =
      if Int.equal n 0 then c
      else match EConstr.kind sg (whd_all env sg ty) with
        | Prod (na, a, b) ->
          let c = EConstr.mkApp (EConstr.Vars.lift 1 c, [|EConstr.mkRel 1|]) in
          EConstr.mkLambda (na, a, eta (push_rel_assum (na, a) env) (n - 1) c b)
        | _ -> assert false
    in
    let c = applistc (EConstr.mkConstU (kn, u)) args in
    extract_term table env sg mle mlt (eta env (needed - la) c (type_of env sg c)) []
  else
    let ctx = gradual_ctx env mle in
    let with_args head rest =
      let rest = List.map (fun a -> extract_maybe_term table env sg mle (new_meta ()) a) rest in
      MLmagic (mlapp (MLmagic head) rest)
    in
    match kind, args with
    | Gradual.GCast, a :: b :: t :: rest ->
      if EConstr.eq_constr sg a b then extract_term table env sg mle mlt t rest
      else
        let ra = gradual_reify table sg ctx a in
        let rb = gradual_reify table sg ctx b in
        let casts = gradual_ind_casts table sg ctx in
        let t = extract_maybe_term table env sg mle (new_meta ()) t in
        with_args (rt_app "cast_with" [casts; ra; rb; MLmagic t]) rest
    | Gradual.GUnknown, a :: rest ->
      with_args (rt_app "unknown_term" [gradual_reify table sg ctx a]) rest
    | Gradual.GErr, a :: rest ->
      with_args (rt_app "err_term" [gradual_reify table sg ctx a]) rest
    | _ -> assert false

(* The runtime description (a [Gradual_rt.ty]) of the type [t]. *)

and gradual_reify table sg ctx t =
  let env = ctx.rt_env in
  let t = whd_all env sg t in
  if info_of_quality (sort_of env sg t) == Logic then rt "erased"
  else match EConstr.kind sg t with
    | Sort s ->
      let s = EConstr.ESorts.kind sg s in
      let n = if Sorts.is_prop s || Sorts.is_sprop s then 0 else if Sorts.is_set s then 1 else 2 in
      rt_app "sort" [MLraw (string_of_int n)]
    | Prod (na, a, b) ->
      let ra = gradual_reify table sg ctx a in
      let ctx', l = rt_push_ml ctx in
      let binding = match flag_of_type env sg a with
        | (Info, Default) -> RtVal (rt_var l)
        | _ -> RtNone
      in
      let ctx' = rt_push ctx' (LocalAssum (na, a)) binding in
      let id = Id (id_of_name na.binder_name) in
      rt_app "pi" [ra; MLlam (id, gradual_reify table sg ctx' b)]
    | Rel n when n <= List.length ctx.rt_binders ->
      begin match snd (List.nth ctx.rt_binders (n - 1)) with
        | RtTy f -> f ctx.rt_depth
        | RtVal _ | RtNone | RtMissing ->
          gradual_error env sg (Pp.str "no runtime description for type") t
      end
    | Rel n ->
      (* A type parameter of the constant being extracted, kept at run time
         (see [gradual_keep_params]); erased ones have a dummy ML type. *)
      let n' = n - List.length ctx.rt_binders in
      begin match Mlenv.get ctx.rt_mle n' with
        | Tdummy _ ->
          gradual_error env sg
            (Pp.str "no runtime description for this type variable \
                     (only type parameters of constants are supported)") t
        | _ -> MLmagic (MLrel (n' + ctx.rt_depth))
      end
    | _ ->
      let hd, args = EConstr.decompose_app sg t in
      match gradual_kind_of_term env sg t, EConstr.kind sg hd with
      | Some Gradual.GUnknown, _ -> rt "unknown_ty"
      | Some Gradual.GErr, _ -> rt "err_ty"
      | _, Const (c, _) when Option.has_some (Gradual.prim_type env c) ->
        begin match Option.get (Gradual.prim_type env c), args with
          | Gradual.PInt, [||] -> rt_app "prim" [MLraw "\"int\""]
          | Gradual.PFloat, [||] -> rt_app "prim" [MLraw "\"float\""]
          | Gradual.PString, [||] -> rt_app "prim" [MLraw "\"string\""]
          | Gradual.PArray, [|a|] -> rt_app "prim_array" [gradual_reify table sg ctx a]
          | _ -> gradual_error env sg (Pp.str "no runtime description for type") t
        end
      | _, Ind (ind, u) ->
        let mib, mip = Inductive.lookup_mind_specif env ind in
        if Array.length args <> mib.mind_nparams + mip.mind_nrealargs then
          gradual_error env sg (Pp.str "partially applied inductive type") t;
        (* Without parameters and indices, all instances are equal and casts
           between them are the identity. *)
        if not (Array.is_empty args)
        && not (List.exists (fun (i, _) -> Ind.CanOrd.equal i ind) !(ctx.rt_needed)) then
          ctx.rt_needed := (ind, u) :: !(ctx.rt_needed);
        let args = Array.map_to_list (gradual_reify_arg table sg ctx) args in
        let data = if gradual_ind_holds_exc table env ind u then "true" else "false" in
        rt_app "branded_ind" [gradual_ind_name_ml env ind;
          MLbrand { glob = GlobRef.IndRef ind; inst = InfvInst.ground (EConstr.EInstance.kind sg u) };
          gradual_ind_representation table env ind u;
          MLraw data; rt_list args]
      | _ -> gradual_error env sg (Pp.str "no runtime description for type") t

(* Can the values of this inductive type be [?] and [err], as data (see
   [Gradual_rt.exc_tag])? Not when they are OCaml values of another type
   (Extract Inductive), unboxed (singleton) or lazy (coinductive), nor when
   the tag of these values could be a constructor's. *)
and gradual_ind_holds_exc table env ind u =
  let inst = InfvInst.ground (EConstr.EInstance.kind (Evd.from_env env) u) in
  let mi = extract_ind table env (fst ind) inst in
  let oi = mi.ind_packets.(snd ind) in
  let non_constant = Array.fold_left (fun n tys ->
      if List.for_all (function Tdummy _ -> true | _ -> false) tys then n else n + 1)
      0 oi.ip_types in
  not (is_custom { glob = GlobRef.IndRef ind; inst })
  && (match mi.ind_kind with Standard | Record _ -> true | Singleton | Coinductive -> false)
  && non_constant < 245

(* A parameter or an index of an inductive type, as a [Gradual_rt.arg]. *)

and gradual_reify_arg table sg ctx a =
  let env = ctx.rt_env in
  match gradual_kind_of_term env sg a with
  | Some Gradual.GUnknown -> rt "unk_arg"
  | Some Gradual.GErr -> rt "err_arg"
  | Some Gradual.GCast | None ->
    match flag_of_type env sg (type_of env sg a) with
    | (Logic, _) -> rt "erased_arg"
    | (Info, TypeScheme) -> rt_app "ty_arg" [gradual_reify table sg ctx a]
    | (Info, Default) -> rt_app "val_arg" [gradual_value table sg ctx a]

(* The value of the term [a], which lives in [ctx.rt_env]: we extract it
   abstracted over [ctx.rt_binders], and apply it to their runtime values. *)

and gradual_value table sg ctx a =
  List.iteri (fun i (_, b) -> match b with
      | RtMissing when not (EConstr.Vars.noccurn sg (i + 1) a) ->
        gradual_error ctx.rt_env sg (Pp.str "the value of an argument is not available") a
      | _ -> ()) ctx.rt_binders;
  let lam = List.fold_left (fun t (d, _) -> EConstr.mkLambda_or_LetIn d t) a ctx.rt_binders in
  let ml = extract_maybe_term table ctx.rt_outer sg ctx.rt_mle (new_meta ()) lam in
  let ml = ast_lift ctx.rt_depth ml in
  let args = List.rev_map (fun (_, b) -> match b with
      | RtVal f -> f ctx.rt_depth
      | RtTy _ | RtNone | RtMissing -> MLdummy Ktype) ctx.rt_binders
  in
  if List.is_empty args then ml else MLapp (MLmagic ml, args)

(* The cast functions of the inductive types needed by the descriptions
   built in [ctx], and of the ones they need in turn, as a list for
   [Gradual_rt.cast_with]. They refer to each other by name, through the
   runtime. *)

and gradual_ind_casts table sg ctx =
  let rec loop is_done acc =
    match List.find_opt (fun (i, _) -> not (List.mem_f Ind.CanOrd.equal i is_done)) !(ctx.rt_needed) with
    | None -> acc
    | Some (ind, u) ->
      let fn = gradual_ind_cast table sg ctx (ind, u) in
      let acc = rt_app "branded_rcons" [gradual_ind_name_ml ctx.rt_outer ind;
          MLbrand { glob = GlobRef.IndRef ind; inst = InfvInst.ground (EConstr.EInstance.kind sg u) };
          gradual_ind_representation table ctx.rt_outer ind u; fn; acc] in
      loop (ind :: is_done) acc
  in
  loop [] (rt "rnil")

(* Equal kernel inductives compiled with incompatible extraction directives
   must not be mistaken for the same OCaml representation through Any. Keep
   this layout ABI independent of the functor's display/qualified names. *)
and gradual_ind_representation table env ind u =
  let inst = InfvInst.ground (EConstr.EInstance.kind (Evd.from_env env) u) in
  let mi = extract_ind table env (fst ind) inst in
  let p = mi.ind_packets.(snd ind) in
  let r = p.ip_typename_ref in
  let custom = if is_custom r then begin
      let args, typ = find_type_custom r in
      let constructors = Array.to_list (Array.map (fun r ->
          try find_custom r with Not_found -> "") p.ip_consnames_ref) in
      let branches = Array.map (fun r -> [], Pusual r, MLdummy Ktype) p.ip_consnames_ref in
      let matching = try find_custom_match branches with Not_found -> "" in
      Some (args, typ, constructors, matching)
    end else None in
  let kind = match mi.ind_kind with
    | Standard -> "variant" | Singleton -> "singleton"
    | Record _ -> "record" | Coinductive -> "coinductive" in
  let retained = Array.to_list (Array.mapi (fun j types ->
      let implicits = implicits_of_global p.ip_consnames_ref.(j) in
      List.mapi (fun k typ ->
          not (isTdummy (expand table env typ)) &&
          not (Int.Set.mem (mi.ind_nparams + k + 1) implicits)) types) p.ip_types) in
  let abi = Marshal.to_string (kind, custom, retained) [Marshal.No_sharing] in
  MLraw (Printf.sprintf "%S" (SomaMerkle.string abi))

(* The function [fun src tgt v -> ...] that rebuilds [v], an inhabitant of
   the instance [src] of the inductive type [ind], at the instance [tgt]:
   the arguments of the constructor are cast from their type in [src] to
   their type in [tgt], and the indices it computes must agree with the
   indices of [tgt]. The function is a closed ML term. *)

and gradual_ind_cast table sg ctx (ind, u) =
  let env = ctx.rt_outer in
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let ind_term = EConstr.mkIndU (ind, u) in
  if mib.mind_finite == Declarations.CoFinite then
    gradual_error env sg (Pp.str "coinductive types are not supported yet") ind_term;
  let inst = InfvInst.ground (EConstr.EInstance.kind sg u) in
  let mi = extract_ind table env (fst ind) inst in
  let oi = mi.ind_packets.(snd ind) in
  let npar = mib.mind_nparams in
  let params_ctx = EConstr.of_rel_context
      (Inductive.inductive_paramdecls (mib, EConstr.EInstance.kind sg u)) in
  if List.length params_ctx <> npar then
    gradual_error env sg (Pp.str "let-ins in parameters are not supported") ind_term;
  (* [fun src tgt v]: levels of these ML variables *)
  let l_src = 1 and l_tgt = 2 in
  let ctx0 = { ctx with rt_env = env; rt_binders = []; rt_depth = 3 } in
  (* The parameters, seen in the source and in the target instance. *)
  let push_params l_d =
    let _, ctx = List.fold_left (fun (k, ctx) decl ->
        let arg f = fun d -> rt_app f [rt_var l_d d; MLraw (string_of_int k)] in
        let b = match flag_of_type ctx.rt_env sg (get_type decl) with
          | (Info, TypeScheme) -> RtTy (arg "param_ty")
          | (Info, Default) -> RtVal (arg "param_val")
          | (Logic, _) -> RtNone
        in
        k + 1, rt_push ctx decl b) (0, ctx0) (List.rev params_ctx)
    in ctx
  in
  let csrc = push_params l_src and ctgt = push_params l_tgt in
  let params = List.init npar (fun k -> EConstr.mkRel (npar - k)) in
  let cstrs = get_constructors csrc.rt_env (make_ind_family ((ind, u), params)) in
  let gind = { glob = GlobRef.IndRef ind; inst } in
  let typ = Tglob (gind, List.map (fun _ -> Tunknown) oi.ip_vars) in
  let branch j cs =
    let r = { glob = GlobRef.ConstructRef (ind, j + 1); inst } in
    let s = List.map (type2sign table env) oi.ip_types.(j) in
    let s = sign_with_implicits r s npar in
    let decls = List.rev cs.cs_args in
    if List.exists is_local_def decls || List.length decls <> List.length s then
      gradual_error env sg (Pp.str "let-ins in constructors are not supported") ind_term;
    (* The arguments [x] of the constructor, as lambdas: for each one, its
       type in the source and the level of [x] if it is kept. *)
    let rec lams csrc acc = function
      | [] -> csrc.rt_depth, List.rev acc
      | (decl, sign) :: l ->
        (* Killed arguments are dummy lambdas, removed by [case_expunge]. *)
        let csrc', lx = rt_push_ml csrc in
        let b, x = match sign with
          | Keep -> RtVal (rt_var lx), Some lx
          | Kill (Kimplicit _) -> RtMissing, None
          | Kill (Ktype | Kprop) -> RtNone, None
        in
        lams (rt_push csrc' decl b) ((decl, sign, csrc, x) :: acc) l
    in
    let depth, args = lams csrc [] (List.combine decls s) in
    (* The casted arguments [y], as let-ins. *)
    let rec lets ctgt ys = function
      | [] -> body ctgt (List.rev ys)
      | (decl, sign, csrc, x) :: l ->
        match x, sign with
        | Some lx, _ ->
          let ty = get_type decl in
          let x = rt_var lx ctgt.rt_depth in
          let y =
            (* The type does not depend on the instance: nothing to cast. *)
            if EConstr.Vars.closed0 sg ty then x
            else
              let ra = gradual_reify table sg { csrc with rt_depth = ctgt.rt_depth } ty in
              let rb = gradual_reify table sg ctgt ty in
              rt_app "cast" [ra; rb; MLmagic x]
          in
          let ctgt', ly = rt_push_ml ctgt in
          let ctgt' = rt_push ctgt' decl (RtVal (rt_var ly)) in
          MLletin (Id (id_of_name (get_name decl)), y, lets ctgt' (ly :: ys) l)
        | None, Kill (Kimplicit _) -> lets (rt_push ctgt decl RtMissing) ys l
        | None, _ -> lets (rt_push ctgt decl RtNone) ys l
    and body ctgt ys =
      let d = ctgt.rt_depth in
      let computed = Array.map_to_list (gradual_reify_arg table sg ctgt) cs.cs_concl_realargs in
      let ys = List.map (fun l -> MLmagic (rt_var l d)) ys in
      let v = if mi.ind_kind == Singleton then
          match ys with
          | [y] -> y
          | _ -> gradual_error env sg
              (Pp.str "a singleton cast must retain exactly one constructor argument") ind_term
        else MLcons (typ, r, ys) in
      rt_app "check_indices" [rt_var l_tgt d; MLraw (string_of_int npar); rt_list computed; MLmagic v]
    in
    let e = lets { ctgt with rt_depth = depth } [] args in
    let e = List.fold_right (fun (decl, _, _, x) e ->
        let id = match x with Some _ -> Id (id_of_name (get_name decl)) | None -> Dummy in
        MLlam (id, e)) args e
    in
    let ids, e = case_expunge s e in
    (List.rev ids, Pusual r, e)
  in
  let v = MLmagic (MLrel 1) in
  let body =
    if Array.length cstrs = 0 then MLexn "absurd case"
    else if mi.ind_kind == Singleton then
      let (ids, _, e) = branch 0 cstrs.(0) in
      (match ids with
       | [id] -> MLletin (tmp_id id, v, e)
       | _ -> gradual_error env sg
           (Pp.str "a singleton cast must retain exactly one constructor argument") ind_term)
    else MLcase (typ, v, Array.mapi branch cstrs)
  in
  let lam s e = MLlam (Id (Id.of_string s), e) in
  lam "src" (lam "tgt" (lam "v" body))

(*S ML declarations. *)

(* [decomp_lams_eta env c t] finds the number [n] of products in the type [t],
   and decompose the term [c] in [n] lambdas, with eta-expansion if needed. *)

let decomp_lams_eta_n n m env sg c t =
  let rels = fst (whd_decompose_prod_n env sg n t) in
  let rels',c = EConstr.decompose_lambda sg c in
  let d = n - m in
  (* we'd better keep rels' as long as possible. *)
  let rels = (List.firstn d rels) @ rels' in
  let eta_args = List.rev_map EConstr.mkRel (List.interval 1 d) in
  rels, applistc (EConstr.Vars.lift d c) eta_args

(* Let's try to identify some situation where extracted code
   will allow generalisation of type variables *)

let rec gentypvar_ok sg c = match EConstr.kind sg c with
  | Lambda _ | Const _ -> true
  | App (c,v) ->
      (* if all arguments are variables, these variables will
         disappear after extraction (see [empty_s] below) *)
      Array.for_all (EConstr.isRel sg) v && gentypvar_ok sg c
  | Cast (c,_,_) -> gentypvar_ok sg c
  | _ -> false

(*s From a constant to a ML declaration. *)

let extract_std_constant table env sg kn inst body typ =
  (* expects body and typ to be already substituted w.r.t. inst *)
  reset_meta_count ();
  (* The short type [t] (i.e. possibly with abbreviations). *)
  let t = snd (record_constant_type table env sg kn inst (Some typ)) in
  (* The real type [t']: without head products, expanded, *)
  (* and with [Tvar] translated to [Tvar'] (not instantiable). *)
  let l,t' = type_decomp (expand table env (var2var' t)) in
  let s = List.map (type2sign table env) l in
  (* Check for user-declared implicit information *)
  let s = sign_with_implicits { glob = GlobRef.ConstRef kn; inst } s 0 in
  (* Decomposing the top level lambdas of [body].
     If there isn't enough, it's ok, as long as remaining args
     aren't to be pruned (and initial lambdas aren't to be all
     removed if the target language is strict). In other situations,
     eta-expansions create artificially enough lams (but that may
     break user's clever let-ins and partial applications). *)
  let rels, c =
    let n = List.length s
    and m = nb_lam sg body in
    if n <= m then decompose_lambda_n sg n body
    else
      let s,s' = List.chop m s in
      if List.for_all ((==) Keep) s' &&
        (lang () == Haskell || sign_kind s != UnsafeLogicalSig)
      then decompose_lambda_n sg m body
      else decomp_lams_eta_n n m env sg body typ
  in
  (* Should we do one eta-expansion to avoid non-generalizable '_a ? *)
  let rels, c =
    let n = List.length rels in
    let s,s' = List.chop n s in
    let k = sign_kind s in
    let empty_s = (k == EmptySig || k == SafeLogicalSig) in
    if lang () == Ocaml && empty_s && not (gentypvar_ok sg c)
      && not (List.is_empty s') && not (Int.equal (type_maxvar t) 0)
    then decomp_lams_eta_n (n+1) n env sg body typ
    else rels,c
  in
  let n = List.length rels in
  let s = List.firstn n s in
  let l,l' = List.chop n l in
  let t' = type_recomp (l',t') in
  (* The initial ML environment. *)
  let mle = List.fold_left Mlenv.push_std_type Mlenv.empty l in
  (* The lambdas names. *)
  let ids = List.map (fun (n,_) -> Id (id_of_name n.binder_name)) rels in
  (* The according Rocq environment. *)
  let env = push_rels_assum rels env in
  (* The real extraction: *)
  let e = extract_term table env sg mle t' c [] in
  (* Expunging term and type from dummy lambdas. *)
  let trm = term_expunge s (ids,e) in
  trm, type_expunge_from_sign table env s t

(* Extracts the type of an axiom, honors the Extraction Implicit declaration. *)
let extract_axiom table env sg kn inst typ =
  reset_meta_count ();
  (* The short type [t] (i.e. possibly with abbreviations). *)
  let t = snd (record_constant_type table env sg kn inst (Some typ)) in
  (* The real type [t']: without head products, expanded, *)
  (* and with [Tvar] translated to [Tvar'] (not instantiable). *)
  let l,_ = type_decomp (expand table env (var2var' t)) in
  let s = List.map (type2sign table env) l in
  (* Check for user-declared implicit information *)
  let s = sign_with_implicits { glob = GlobRef.ConstRef kn; inst } s 0 in
  type_expunge_from_sign table env s t

let extract_fixpoint table env sg vkn inst (fi,ti,ci) =
  let n = Array.length vkn in
  let types = Array.make n (Tdummy Kprop)
  and terms = Array.make n (MLdummy Kprop) in
  let kns = Array.to_list vkn in
  current_fixpoints := kns;
  (* for replacing recursive calls [Rel ..] by the corresponding [Const]: *)
  let sg, sub = CList.fold_left_map (fun sg con ->
      Evd.fresh_global env sg (ConstRef con))
      sg
      (List.rev kns)
  in
  for i = 0 to n-1 do
    if info_of_quality (sort_of env sg ti.(i)) != Logic then
      try
        let e,t = extract_std_constant table env sg vkn.(i) inst
                   (EConstr.Vars.substl sub ci.(i)) ti.(i) in
        terms.(i) <- e;
        types.(i) <- t;
      with SingletonInductiveBecomesProp ind ->
        error_singleton_become_prop ind
  done;
  current_fixpoints := [];
  Dfix (Array.map (fun kn -> { glob = GlobRef.ConstRef kn; inst }) vkn, terms, types)

let extract_constant table access env kn inst cb =
  let sg = Evd.from_env env in
  let r = { glob = GlobRef.ConstRef kn; inst } in
  let typ = qmono cb.const_universes inst cb.const_type in
  let warn_info () = if not (is_custom r) then add_info_axiom (Common.State.get_table table) r.glob in
  let warn_log () = if not (constant_has_body cb) then add_log_axiom (Common.State.get_table table) r.glob
  in
  let mk_typ_ax () =
    let n = type_scheme_nb_args env sg typ in
    let ids = iterate (fun l -> anonymous_name::l) n [] in
    Dtype (r, ids, Taxiom)
  in
  let mk_typ c =
    let s,vl = type_sign_vl env sg typ in
    let db = db_from_sign s in
    let t = extract_type_scheme table env sg db c (List.length s)
    in Dtype (r, vl, t)
  in
  let mk_ax () =
    let t = extract_axiom table env sg kn inst typ in
    Dterm (r, MLaxiom (Constant.to_string kn), t)
  in
  let mk_def c =
    let e,t = extract_std_constant table env sg kn inst c typ in
    Dterm (r,e,t)
  in
  try
    match flag_of_type env sg typ with
    | (Logic,TypeScheme) -> warn_log ();
        let s,vl = type_sign_vl env sg typ in
        Dtype (r, vl, Tdummy Ktype)
    | (Logic,Default) -> warn_log (); Dterm (r, MLdummy Kprop, Tdummy Kprop)
    | (Info,TypeScheme) ->
        (match cb.const_body with
          | Symbol _ -> add_symbol (Common.State.get_table table) r.glob; mk_typ_ax ()
          | Primitive _ | Undef _ -> warn_info (); mk_typ_ax ()
          | Def c ->
             (match Structures.PrimitiveProjections.find_opt kn with
              | None -> mk_typ (qmono cb.const_universes inst c)
              | Some p ->
                let body = fake_match_projection env p in
                let body = qmono cb.const_universes inst body in
                mk_typ body)
          | OpaqueDef c ->
            add_opaque (Common.State.get_table table) r.glob;
            if access_opaque () then mk_typ (get_opaque cb.const_universes inst access c)
            else mk_typ_ax ())
    | (Info,Default) ->
        (match cb.const_body with
          | Symbol _ -> add_symbol (Common.State.get_table table) r.glob; mk_ax ()
          | Primitive _ | Undef _ -> warn_info (); mk_ax ()
          | Def c ->
             (match Structures.PrimitiveProjections.find_opt kn with
              | None -> mk_def (qmono cb.const_universes inst c)
              | Some p ->
                let body = fake_match_projection env p in
                mk_def (qmono cb.const_universes inst body))
          | OpaqueDef c ->
            add_opaque (Common.State.get_table table) r.glob;
            if access_opaque () then mk_def (get_opaque cb.const_universes inst access c)
            else mk_ax ())
  with SingletonInductiveBecomesProp ind ->
    error_singleton_become_prop ind

let extract_constant_spec table env kn inst cb =
  let sg = Evd.from_env env in
  let r = { glob = GlobRef.ConstRef kn; inst } in
  let typ = qmono cb.const_universes inst cb.const_type in
  try
    match flag_of_type env sg typ with
    | (Logic, TypeScheme) ->
        let s,vl = type_sign_vl env sg typ in
        Stype (r, vl, Some (Tdummy Ktype))
    | (Logic, Default) -> Sval (r, Tdummy Kprop)
    | (Info, TypeScheme) ->
        let s,vl = type_sign_vl env sg typ in
        (match cb.const_body with
          | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> Stype (r, vl, None)
          | Def body ->
              let db = db_from_sign s in
              let body = qmono cb.const_universes inst body in
              let t = extract_type_scheme table env sg db body (List.length s)
              in Stype (r, vl, Some t))
    | (Info, Default) ->
        let t = snd (record_constant_type table env sg kn inst (Some typ)) in
        Sval (r, type_expunge table env t)
  with SingletonInductiveBecomesProp ind ->
    error_singleton_become_prop ind

let extract_with_type table env sg c =
  try
    let typ = type_of env sg c in
    match flag_of_type env sg typ with
    | (Info, TypeScheme) ->
        let s,vl = type_sign_vl env sg typ in
        let db = db_from_sign s in
        let t = extract_type_scheme table env sg db c (List.length s) in
        Some (vl, t)
    | _ -> None
  with SingletonInductiveBecomesProp ind ->
    error_singleton_become_prop ind

let extract_constr table env sg c =
  reset_meta_count ();
  try
    let typ = type_of env sg c in
    match flag_of_type env sg typ with
    | (_,TypeScheme) -> MLdummy Ktype, Tdummy Ktype
    | (Logic,_) -> MLdummy Kprop, Tdummy Kprop
    | (Info,Default) ->
       let mlt = extract_type table env sg [] 1 typ [] in
       extract_term table env sg Mlenv.empty mlt c [], mlt
  with SingletonInductiveBecomesProp ind ->
    error_singleton_become_prop ind

let extract_inductive table env kn inst =
  let ind = extract_ind table env kn inst in
  let () = add_recursors (Common.State.get_table table) env kn in
  let f i j l =
    let r = { glob = GlobRef.ConstructRef ((kn, i), j + 1); inst } in
    filter_extracted_constructor_types table env ind.ind_nparams r l
  in
  let packets =
    Array.mapi (fun i p -> { p with ip_types = Array.mapi (f i) p.ip_types })
      ind.ind_packets
  in { ind with ind_packets = packets }

(*s Is a [ml_decl] logical ? *)

let logical_decl = function
  | Dterm (_,MLdummy _,Tdummy _) -> true
  | Dtype (_,_,Tdummy _) -> true
  | Dfix (_,av,tv) ->
      (Array.for_all isMLdummy av) &&
      (Array.for_all isTdummy tv)
  | Dind i -> Array.for_all (fun ip -> ip.ip_logical) i.ind_packets
  | _ -> false

(*s Is a [ml_spec] logical ? *)

let logical_spec = function
  | Stype (_, _, Some (Tdummy _)) -> true
  | Sval (_,Tdummy _) -> true
  | Sind i -> Array.for_all (fun ip -> ip.ip_logical) i.ind_packets
  | _ -> false
